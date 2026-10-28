-- Prove2me | Theorems.Thm_KKM_exists_mem_convexHull_mem_iInter
-- name    : KKM.exists_mem_convexHull_mem_iInter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T04:08:07.107618+00:00
-- url     : https://prove2.me/theorems/4d89dd0e-b61e-4fb0-b081-279429ab7227
-- title:
--   The KKM covering lemma in a topological vector space
-- statement:
--   Let $E$ be a real topological vector space, let $a_0, \dots, a_n \in E$ be arbitrary
--   points, and write $C = \operatorname{conv}\{a_0, \dots, a_n\}$ for their convex hull. Let
--   $A_0, \dots, A_n \subseteq E$ be open sets with
--
--   1. $C \subseteq \bigcup_i A_i$;
--   2. $C \setminus A_i$ convex for every $i$;
--   3. $a_i \notin A_j$ whenever $i \ne j$.
--
--   Then they have a common point *in the hull*:
--
--   $$
--   \exists\, z \in C \ \text{ such that } \ z \in A_i \ \text{ for every } i .
--   $$
--
--   Two things make this the usable form. The ambient space is any topological vector space, with
--   no inner product, no norm and no finite-dimensionality assumed; and the points $a_i$ are
--   arbitrary — **no affine independence is required**, so the hull may be a degenerate
--   simplex. The conclusion locating the common point inside $C$, rather than merely asserting that
--   the intersection is nonempty, is what lets the lemma be applied to a subset of the hull in the
--   next step of a minimax argument.
--
--   **Formalization Note** The hypotheses on $E$ are `AddCommGroup`, `Module ℝ`,
--   `TopologicalSpace`, `IsTopologicalAddGroup` and `ContinuousSMul ℝ`; $C$ is
--   `convexHull ℝ (Set.range a)`.
-- source:
--   B. Knaster, C. Kuratowski and S. Mazurkiewicz, Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe, Fund. Math. 14 (1929), 132–137; M. Sion, On general minimax theorems, Pacific J. Math. 8 (1958), 171–176, Theorem 3.1 (p. 173). Carved from the accepted proof of SionMinimax.KKM.lemma_3_3, https://prove2.me/submissions/818ed08f-1f44-45cc-90a9-3239f8bb6e07

import Mathlib

theorem KKM.exists_mem_convexHull_mem_iInter {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (n : ℕ) (a : Fin (n + 1) → E)
    (A : Fin (n + 1) → Set E)
    (hA : ∀ i, IsOpen (A i))
    (hcov : convexHull ℝ (Set.range a) ⊆ ⋃ i, A i)
    (hconv : ∀ i, Convex ℝ (convexHull ℝ (Set.range a) \ A i))
    (hv : ∀ i j, i ≠ j → a i ∉ A j) :
    ∃ z ∈ convexHull ℝ (Set.range a), ∀ i, z ∈ A i := by sorry
