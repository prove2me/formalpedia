-- Prove2me | Theorems.Thm_JohnsonApprox_ExactCover_uncov_card_bound_of_ratio_ge
-- name    : JohnsonApprox.ExactCover.uncov_card_bound_of_ratio_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:32:05.221044+00:00
-- url     : https://prove2.me/theorems/0938ec80-4f0b-452b-a9d5-b3a51eb935b4
-- title:
--   Proof of Theorem 6 — if C2 may choose a set of ratio ≥ y, then |UNCOV| ≤ F*/(y + 1)
-- statement:
--   Let $F$ be an input of SET COVERING II with optimum $F^*$. Suppose that at some state reachable by algorithm C2 on $F$, C2 may choose the set $S'$ at Step 3, and let $y$ be a real number with
--   $$\mathrm{Ratio}(S') = \frac{|S' - \mathrm{UNCOV}|}{|S' \cap \mathrm{UNCOV}|} \ge y.$$
--   Then, at that moment,
--   $$(y + 1)\,|\mathrm{UNCOV}| \le F^*,$$
--   i.e. $|\mathrm{UNCOV}| \le F^*/(y+1)$ when $y + 1 > 0$.
--
--   In the paper this comes from comparing the chosen set with the sets of an optimal subcover $F_0$: each of them has at most a $1/(y+1)$ fraction of its points still uncovered. The bound says that C2 cannot be forced into high-overlap choices until most of $T$ is covered.
--
--   **Formalization Note** "Ratio$(S') \ge y$" is written $y \cdot |S' \cap \mathrm{UNCOV}| \le |S' - \mathrm{UNCOV}|$ and the conclusion multiplicatively, so no division occurs; C2 may only choose sets meeting UNCOV, so the ratio is finite. No sign condition on $y$ is needed: for $y \le -1$ the conclusion is trivially true.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 271, proof of Theorem 6

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 271): if C2 may choose `S′` with `Ratio(S′) ≥ y`, then
`|UNCOV| ≤ F*/(y + 1)` (stated multiplicatively). -/
theorem uncov_card_bound_of_ratio_ge {α : Type} [DecidableEq α] (F : Input α)
    {σ : State F} {i : Fin F.p} (hσ : Reachable F σ) (hi : MayChoose F σ i) (y : ℝ)
    (hy : y * ((F.S i ∩ σ.UNCOV).card : ℝ) ≤ ((F.S i \ σ.UNCOV).card : ℝ)) :
    (y + 1) * (σ.UNCOV.card : ℝ) ≤ (F.opt : ℝ) := by sorry

end JohnsonApprox.ExactCover
