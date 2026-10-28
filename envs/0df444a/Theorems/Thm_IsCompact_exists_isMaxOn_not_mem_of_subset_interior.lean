-- Prove2me | Theorems.Thm_IsCompact_exists_isMaxOn_not_mem_of_subset_interior
-- name    : IsCompact.exists_isMaxOn_not_mem_of_subset_interior
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:00.641534+00:00
-- url     : https://prove2.me/theorems/9ff5ecc7-9876-4580-9fd0-ab09942f56ab
-- title:
--   A linear functional attains its maximum on a compact set outside any interior part
-- statement:
--   Let $E$ be a nontrivial real normed space, let $K \subseteq E$ be nonempty and compact, let
--   $D \subseteq \operatorname{int} K$, and let $\ell : E \to \mathbb{R}$ be a continuous linear
--   functional. Then $\ell$ attains its maximum over $K$ at a point that is not in $D$:
--
--   $$
--   \exists\, x \in K, \ x \notin D, \ \text{ such that } \ \ell(y) \le \ell(x) \quad
--   \text{for every } y \in K .
--   $$
--
--   The maximum of a linear functional over a compact set is attained on the boundary, so no
--   maximizer can be forced into a set buried in the interior -- but that reading needs the
--   functional to be nonzero, and the statement here needs no such hypothesis: when $\ell = 0$ every
--   point is a maximizer and compactness alone supplies one outside $D$. It is the step that lets an
--   argument choose an extremal point avoiding a prescribed interior region, which is how worst-case
--   distributions get pushed to the boundary of a moment set.
-- source:
--   S. Zymler, D. Kuhn and B. Rustem, Distributionally robust joint chance constraints with second-order moment information, Mathematical Programming 137 (2013), 167-198. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 3927-3983 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open MeasureTheory Matrix
open scoped ENNReal

theorem IsCompact.exists_isMaxOn_not_mem_of_subset_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {Kc : Set E} (hK : IsCompact Kc) (hne : Kc.Nonempty) {D : Set E}
    (hD : D ⊆ interior Kc) (ℓ : E →L[ℝ] ℝ) :
    ∃ x ∈ Kc, x ∉ D ∧ ∀ y ∈ Kc, ℓ y ≤ ℓ x := by sorry
