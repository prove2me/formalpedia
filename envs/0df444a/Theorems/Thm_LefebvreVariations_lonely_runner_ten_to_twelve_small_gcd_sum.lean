-- Prove2me | Theorems.Thm_LefebvreVariations_lonely_runner_ten_to_twelve_small_gcd_sum
-- name    : LefebvreVariations.lonely_runner_ten_to_twelve_small_gcd_sum
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:01:08.831069+00:00
-- url     : https://prove2.me/theorems/04cd8126-6844-400f-9bbb-6c28c7c00dfb
-- title:
--   Lefebvre's variations, No. 126 — on a theme by Rosenfeld: the lonely runner with eleven to thirteen runners, coprime speeds of small gcd-sum
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   For a real number $x$ write $\|x\|$ for its distance to the nearest integer. Let $n\in\{10,11,12\}$ and assume the lonely runner conjecture for $n-1$ moving runners: every set of $n-1$ distinct positive integers admits a $t$ with $\|tv\|\ge \frac1n$ for all its elements.
--
--   Then for every $v_1,\dots,v_n\in\mathbb{Z}_{>0}$ with $\gcd(v_1,\dots,v_n)=1$ and $\sum_{S\subseteq[n]}\gcd(v_i:i\in S)\le\binom{n+1}{2}^{n-1}$ there is $t\in\mathbb{R}$ with $\|t v_i\|\ge\frac1{n+1}$ for all $i$.
--
--   This is the lonely runner conjecture for $n=10,11,12$ moving runners (eleven, twelve and thirteen runners; Sungkawichai–Trakulthongchai 2026), restricted to the finite range not covered by the Malikiosis–Santos–Schymura reduction, and granted the case of one runner fewer.
--
--   **Formalization Note** The distance to the nearest integer is `LonelyRunnerConjecture.distToNearestInt x = min (fract x) (1 - fract x)`, i.e. $\|x\|$. The speeds are a function `v : Fin n → ℕ` (as in `LonelyRunnerConjecture.mss_finite_checking`, so repetitions are allowed; this does not change the truth, because fewer than $n$ distinct speeds only weakens the bound $1/(n+1)$). `Finset.gcd Finset.univ v` is $\gcd(v_1,\dots,v_n)$, and the sum over `Finset.univ.powerset` runs over all subsets $S\subseteq[n]$, with `Finset.gcd ∅ v = 0` so the empty set contributes nothing.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `LonelyRunnerConjecture.eleven_twelve_thirteen` (the lonely runner conjecture for eleven, twelve and thirteen runners). The Lean-verified reduction proves the base statement from the open platform theorems `trakulthongchai_nine_ten` and `mss_finite_checking`, and from this statement, which covers the finite remaining half (small gcd-sum, with the case of one fewer runner as hypothesis). It is a special case of the base statement, and the base statement follows from it together with those inputs.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). Statement true by Sungkawichai and Trakulthongchai, the lonely runner conjecture for eleven, twelve and thirteen runners (2026, as stated in the platform milestone), given the preceding case. It is the finite range left by N. Malikiosis, M. Santos, M. Schymura, Theorem A. Citations from memory (no network). Origin of this statement: it is the missing step of a reduction of `LonelyRunnerConjecture.eleven_twelve_thirteen` (LRC 10 ∧ LRC 11 ∧ LRC 12). Malikiosis–Santos–Schymura (Theorem A, platform theorem `LonelyRunnerConjecture.mss_finite_checking`) handles every gcd-one speed vector whose gcd-sum exceeds C(n+1,2)^(n-1) once LRC(n-1) is known; what is left is the finite range gcd-sum ≤ C(n+1,2)^(n-1). The file `lonely_runner_ten_to_twelve_small_gcd_sum_reduction.lean` derives `LonelyRunnerConjecture.eleven_twelve_thirteen` (LRC 10 ∧ LRC 11 ∧ LRC 12) from this statement, `mss_finite_checking` and `trakulthongchai_nine_ten` (for LRC 9); the Lean proof of the gcd-normalisation (divide by g = gcd S) and the case split is complete.

import Definitions.Def_LonelyRunnerConjecture_Defs

set_option autoImplicit false

namespace LefebvreVariations
theorem lonely_runner_ten_to_twelve_small_gcd_sum (n : ℕ) (hlo : 10 ≤ n) (hhi : n ≤ 12)
    (hprev : LonelyRunnerConjecture.LRC (n - 1))
    (v : Fin n → ℕ) (hpos : ∀ i, 0 < v i)
    (hgcd : Finset.gcd Finset.univ v = 1)
    (hsum : (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) ≤ Nat.choose (n + 1) 2 ^ (n - 1)) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤
      LonelyRunnerConjecture.distToNearestInt (t * (v i : ℝ)) := by sorry
end LefebvreVariations
