-- Prove2me | Theorems.Thm_LefebvreVariations_lonely_runner_eight_nine_small_gcd_sum
-- name    : LefebvreVariations.lonely_runner_eight_nine_small_gcd_sum
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:59:38.871358+00:00
-- url     : https://prove2.me/theorems/b1b59f22-b5f7-5f63-b90f-49bcde08374f
-- title:
--   Lefebvre's variations, No. 105 — on a theme by Rosenfeld: the lonely runner with nine and ten runners, coprime speeds of small gcd-sum
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   For a real number $x$ write $\|x\|$ for its distance to the nearest integer. Let $n\in\{8,9\}$ and assume the lonely runner conjecture for $n-1$ moving runners: every set of $n-1$ distinct positive integers admits a $t$ with $\|tv\|\ge \frac1n$ for all its elements.
--
--   Then for every $v_1,\dots,v_n\in\mathbb{Z}_{>0}$ with $\gcd(v_1,\dots,v_n)=1$ and $\sum_{S\subseteq[n]}\gcd(v_i:i\in S)\le\binom{n+1}{2}^{n-1}$ there is $t\in\mathbb{R}$ with $\|t v_i\|\ge\frac1{n+1}$ for all $i$.
--
--   This is the lonely runner conjecture for $n=8$ and $n=9$ moving runners (nine and ten runners; Trakulthongchai 2025), restricted to the finite range not covered by the Malikiosis–Santos–Schymura reduction, and granted the case of one runner fewer.
--
--   **Formalization Note** The distance to the nearest integer is `LonelyRunnerConjecture.distToNearestInt x = min (fract x) (1 - fract x)`, i.e. $\|x\|$. The speeds are a function `v : Fin n → ℕ` (as in `LonelyRunnerConjecture.mss_finite_checking`, so repetitions are allowed; this does not change the truth, because fewer than $n$ distinct speeds only weakens the bound $1/(n+1)$). `Finset.gcd Finset.univ v` is $\gcd(v_1,\dots,v_n)$, and the sum over `Finset.univ.powerset` runs over all subsets $S\subseteq[n]$, with `Finset.gcd ∅ v = 0` so the empty set contributes nothing.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `LonelyRunnerConjecture.trakulthongchai_nine_ten` (the lonely runner conjecture for nine and ten runners). The Lean-verified reduction proves the base statement from the open platform theorems `rosenfeld_eight_runners` (for $k=7$) and `mss_finite_checking`, and from this statement, which covers the finite remaining half (small gcd-sum, with the case of one fewer runner as hypothesis). It is a special case of the base statement, and the base statement follows from it together with those inputs.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). Statement true by W. Trakulthongchai, The lonely runner conjecture holds for nine and ten runners (2025), given the preceding case (Rosenfeld 2025 for n=8; the n=9 instance uses n=8). It is the finite range left by N. Malikiosis, M. Santos, M. Schymura, Theorem A. Citations from memory (no network). Origin of this statement: it is the missing step of a reduction of `LonelyRunnerConjecture.trakulthongchai_nine_ten` (LRC 8 ∧ LRC 9). Malikiosis–Santos–Schymura (Theorem A, platform theorem `LonelyRunnerConjecture.mss_finite_checking`) handles every gcd-one speed vector whose gcd-sum exceeds C(n+1,2)^(n-1) once LRC(n-1) is known; what is left is the finite range gcd-sum ≤ C(n+1,2)^(n-1). The file `lonely_runner_eight_nine_small_gcd_sum_reduction.lean` derives `LonelyRunnerConjecture.trakulthongchai_nine_ten` (LRC 8 ∧ LRC 9) from this statement, `mss_finite_checking` and `rosenfeld_eight_runners` (for LRC 7); the Lean proof of the gcd-normalisation (divide by g = gcd S) and the case split is complete.

import Definitions.Def_LonelyRunnerConjecture_Defs

set_option autoImplicit false

namespace LefebvreVariations
theorem lonely_runner_eight_nine_small_gcd_sum (n : ℕ) (hlo : 8 ≤ n) (hhi : n ≤ 9)
    (hprev : LonelyRunnerConjecture.LRC (n - 1))
    (v : Fin n → ℕ) (hpos : ∀ i, 0 < v i)
    (hgcd : Finset.gcd Finset.univ v = 1)
    (hsum : (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) ≤ Nat.choose (n + 1) 2 ^ (n - 1)) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤
      LonelyRunnerConjecture.distToNearestInt (t * (v i : ℝ)) := by sorry
end LefebvreVariations
