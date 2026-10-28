-- Prove2me | Theorems.Thm_KKM_iInter_nonempty
-- name    : KKM.iInter_nonempty
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:08:05.391537+00:00
-- url     : https://prove2.me/theorems/91e539a0-349a-48d2-94a7-4cd2e8e44b2f
-- title:
--   The Knaster–Kuratowski–Mazurkiewicz lemma, without affine independence
-- statement:
--   **The KKM lemma.** Let $E$ be a real topological vector space, let
--   $a_0, \dots, a_n \in E$ and let $A_0, \dots, A_n$ be open sets such that the convex hull
--   $C = \operatorname{conv}\{a_0,\dots,a_n\}$ is covered by the $A_i$, each $C \setminus A_i$ is
--   convex, and $a_i \notin A_j$ for $i \ne j$. Then
--
--   $$
--   \bigcap_{i=0}^{n} A_i \;\ne\; \varnothing .
--   $$
--
--   The affine independence of the points $a_i$ is **not** assumed. That matters in use: a minimax
--   or equilibrium argument produces a family of sets indexed by the points of a finite set that
--   need not be in general position, and checking independence is exactly the step one cannot
--   perform. The platform's `SionMinimax.KKM.theorem_3_1` is this statement with
--   `AffineIndependent ℝ a` added as a hypothesis, so this version implies it immediately and
--   the hypothesis can be dropped wherever it was being carried.
--
--   Together with Brouwer's fixed point theorem, on which it rests here, this is the standard entry
--   point to Sion's minimax theorem and to the KKM-type existence results used for Nash equilibria
--   and variational inequalities.
-- source:
--   B. Knaster, C. Kuratowski and S. Mazurkiewicz, Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe, Fund. Math. 14 (1929), 132–137; M. Sion, On general minimax theorems, Pacific J. Math. 8 (1958), 171–176, Theorem 3.1 (p. 173). Carved from the accepted proof of SionMinimax.KKM.lemma_3_3, https://prove2.me/submissions/818ed08f-1f44-45cc-90a9-3239f8bb6e07

import Mathlib

theorem KKM.iInter_nonempty {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    (⋂ i, A i).Nonempty := by sorry
