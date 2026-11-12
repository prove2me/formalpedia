-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_theorem_3_5
-- name    : MinCostArbPacking.Main.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:22.526317+00:00
-- url     : https://prove2.me/theorems/1e14c310-a897-48f8-8cef-0c843a76b519
-- title:
--   Theorem 3.5 — weighted matroid intersection: augmenting paths, extremality, shortest augmentations [Sch03]
-- statement:
--   **Theorem 3.5** ([Sch03, Theorems 41.2–41.3 and 41.5–41.6], cited). Let $M_1,M_2$ be matroids on a finite set $E$ and $c:E\to\mathbb R$.
--
--   1. A common independent set $I$ has maximum cardinality iff $D(I)$ has no augmenting path.
--   2. A common independent set $I$ is extreme iff $D(I)$ has no negative cycle.
--   3. If $I$ is extreme and $P$ is a shortest augmenting path (minimum $\ell(P)$, then minimum $q(P)$), then
--   $$I\oplus P\ \text{is an extreme common independent set with } |I\oplus P|=|I|+1.$$
--
--   This is the classical weighted matroid intersection theory on which the relaxation theorem is built.
--
--   **Formalization Note** Matroids are Mathlib `Matroid`s with ground set the whole finite type.
--
--   Differences from the source:
--   - encoding: matroids on $E$; paths and cycles of $D(I)$ → Mathlib matroids with ground set `univ`; paths and cycles as duplicate-free lists; reason: the same objects
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.3, p.8, Theorem 3.5 (cited: Schrijver, Combinatorial Optimization, Thms 41.2–41.3, 41.5–41.6)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Theorem 3.5 ([Sch03, Theorems 41.2–41.3 and 41.5–41.6]), p.8, for two matroids `M₁, M₂` on
the finite ground set `α` and costs `c`: a common independent set has maximum cardinality iff
`D(I)` has no augmenting path; it is extreme iff `D(I)` has no negative cycle; and if `I` is
extreme and `P` is a shortest augmenting path, then `I ⊕ P` is an extreme common independent set of
size `|I| + 1`. -/
theorem theorem_3_5 {α : Type} [Fintype α] [DecidableEq α] (M₁ M₂ : Matroid α) (h₁ : M₁.E = Set.univ) (h₂ : M₂.E = Set.univ)
    (c : α → ℝ) :
    (∀ I, CommonIndep (matInd M₁) (matInd M₂) I →
      (IsMaxCommon (matInd M₁) (matInd M₂) I ↔ ¬ ∃ P, IsAugPath (matInd M₁) (matInd M₂) I P)) ∧
    (∀ I, CommonIndep (matInd M₁) (matInd M₂) I →
      (IsExtreme (matInd M₁) (matInd M₂) c I ↔
        ¬ ∃ C, IsCycleE (exArc (matInd M₁) (matInd M₂) I) C ∧ cycleWeight c I C < 0)) ∧
    (∀ I P, IsExtreme (matInd M₁) (matInd M₂) c I →
      IsShortestAmong (IsAugPath (matInd M₁) (matInd M₂) I) c I P →
        IsExtreme (matInd M₁) (matInd M₂) c (symmDiff I P.toFinset) ∧
          (symmDiff I P.toFinset).card = I.card + 1) := by sorry

end MinCostArbPacking.Main
