-- Prove2me | Theorems.Thm_LefebvreVariations_lonely_runner_seven_small_gcd_sum
-- name    : LefebvreVariations.lonely_runner_seven_small_gcd_sum
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:29:02.387813+00:00
-- url     : https://prove2.me/theorems/cf412d5a-5a9a-5d27-84f0-322375717305
-- title:
--   Lefebvre's variations, No. 80 — on a theme by Wills: the lonely runner with seven runners, coprime speeds of small gcd-sum
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   For a real number $x$ write $\|x\|$ for its distance to the nearest integer.
--
--   Let $v_1,\dots,v_7$ be positive integers with $\gcd(v_1,\dots,v_7)=1$ and
--   $$\sum_{S\subseteq[7]} \gcd(v_i : i\in S) \;\le\; \binom{8}{2}^{6}=28^6 ,$$
--   where the empty subset contributes $0$. Then there is a real $t$ with $\|t v_i\|\ge \frac18$ for all $i=1,\dots,7$.
--
--   This is the lonely runner conjecture for seven moving runners (eight in all; Rosenfeld 2025), restricted to the finite range of speed vectors with small gcd-sum, the range that is not covered by the Malikiosis–Santos–Schymura reduction (which settles all gcd-one vectors with gcd-sum above $28^6$ once six runners are known).
--
--   **Formalization Note** The distance to the nearest integer is `LonelyRunnerConjecture.distToNearestInt x = min (fract x) (1 - fract x)`, i.e. $\|x\|$. The speeds are a function `v : Fin n → ℕ` (as in `LonelyRunnerConjecture.mss_finite_checking`, so repetitions are allowed; this does not change the truth, because fewer than $n$ distinct speeds only weakens the bound $1/(n+1)$). `Finset.gcd Finset.univ v` is $\gcd(v_1,\dots,v_n)$, and the sum over `Finset.univ.powerset` runs over all subsets $S\subseteq[n]$, with `Finset.gcd ∅ v = 0` so the empty set contributes nothing.
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `LonelyRunnerConjecture.rosenfeld_eight_runners` (the lonely runner conjecture for seven moving runners). The Lean-verified reduction proves the base statement from the proved case of six runners (`classical_small_cases`), from the open platform theorem `mss_finite_checking` (Malikiosis–Santos–Schymura), which covers speed vectors with large gcd-sum, and from this statement, which covers the finite remaining half: coprime vectors of seven speeds with gcd-sum at most $28^6$. It is a special case of the base statement, and the base statement follows from it together with those two inputs.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). Statement true by D. Rosenfeld, The lonely runner conjecture holds for eight runners (2025) (LRC(7)), together with the cases up to six moving runners (Barajas–Serra); it is the part of that theorem left after the reduction of N. Malikiosis, M. Santos, M. Schymura, Linear programming bounds / On the lonely runner conjecture (Theorem A: gcd-one vectors with sum of subset gcds above C(n+1,2)^(n-1) follow from LRC(n-1)). Citations from memory (no network). Origin of this statement: it is the missing step of a reduction of `LonelyRunnerConjecture.rosenfeld_eight_runners` (LRC 7). Malikiosis–Santos–Schymura (Theorem A, platform theorem `LonelyRunnerConjecture.mss_finite_checking`) handles every gcd-one speed vector whose gcd-sum exceeds C(n+1,2)^(n-1) once LRC(n-1) is known; what is left is the finite range gcd-sum ≤ C(n+1,2)^(n-1). The file `lonely_runner_seven_small_gcd_sum_reduction.lean` derives `LonelyRunnerConjecture.rosenfeld_eight_runners` (LRC 7) from this statement, `mss_finite_checking` and `classical_small_cases` (for LRC 6); the Lean proof of the gcd-normalisation (divide by g = gcd S) and the case split is complete.

import Definitions.Def_LonelyRunnerConjecture_Defs

set_option autoImplicit false

namespace LefebvreVariations
theorem lonely_runner_seven_small_gcd_sum (v : Fin 7 → ℕ) (hpos : ∀ i, 0 < v i)
    (hgcd : Finset.gcd Finset.univ v = 1)
    (hsum : (∑ S ∈ Finset.univ.powerset, Finset.gcd S v) ≤ Nat.choose (7 + 1) 2 ^ (7 - 1)) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / (7 + 1 : ℝ) ≤
      LonelyRunnerConjecture.distToNearestInt (t * (v i : ℝ)) := by sorry
end LefebvreVariations
