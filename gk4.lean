import Mathlib
noncomputable section
open Nat BigOperators
open Real
open Nat Finset

def S: ℕ → ℝ
| 1    =>  1
| n+1  =>  2*S (n) +n +1
| _    =>  0

def a :ℕ → ℝ
| 1    =>  1
| n+1  =>  S (n+1) - S (n)
| _    =>  0

lemma S_zero (n : ℕ) (hn : 0 ≤ n): S n ≥ 0 :=by
    induction n with
    | zero =>
      have h: S (0)=0 :=by simp[S]
      linarith
    | succ n ih =>
      match n with
      |0 =>
       have h1: S (0 + 1) =1 := by simp[S]
       linarith
      |m+1  =>
        have hm2 : 0 ≤ m + 1 := by  norm_num
        have h2 : m+1+1 =m+2 := rfl
        rw[h2]
        apply ih at hm2
        have h3: S (m+2)=2*S (m+1) +m+1+1 :=by
          simp[S]
          linarith
        linarith

theorem dengbi  (n : ℕ) (hn : 1 ≤ n) :  (a (n+1)+1)/(a (n)+1)= 2 :=by
  induction n with
  | zero =>
    contradiction
  | succ n ih =>
    match n with
    | 0 =>
      have h1: a 1 = 1 := by simp[a]
      have h2: S 1= 1 := by simp[S]
      have h3: S 2= 4:=by
        have h4 : S 2 = 2 * S (1) + 1 + 1 :=by simp[S]
        linarith
      have h5 : a 2=3 :=by
        have h6: a 2= S 2 - S 1 := by simp[a]
        linarith
      rw[h1]
      rw[h5]
      norm_num
    | m+1 =>
      have h7:a (m+1+1+1)= S (m+1+1+1) - S (m+1+1) :=rfl
      have h8:a (m+1+1)= S (m+1+1)- S (m+1):=rfl
      rw[h7]
      rw[h8]
      have h9: S (m+1+1+1) = 2* S (m+1+1) + m+1+1 +1 := by
        simp [S]
        linarith
      have h10: S (m+1+1) = 2* S (m+1) + m+1 +1 := by
        simp [S]
        linarith
      have h11:S (m + 1 + 1 + 1) - S (m + 1 + 1) + 1= S (m+1+1) +m +4 :=by
        simp[S]
        linarith
      rw[h11]
      have h12: S (m+1+1) +m +4 = 2* S (m+1) + 2*m +6 := by
        simp[S]
        linarith
      rw[h12]
      have h13: S (m + 1 + 1) - S (m + 1) + 1 = S (m+1) +m + 3:= by
        simp[S]
        linarith
      rw[h13]
      have h14: 2* S (m+1) + 2*m +6 = 2*(S (m+1) +m + 3):=by linarith
      rw[h14]
      have h15: S (m+1) +m + 3≠ 0:=by
        have h16: S (m+1) ≥0 :=by
          have h17: 0≤m + 1:=by
            linarith
          exact S_zero (m+1) h17
        linarith
      field_simp [h15]
