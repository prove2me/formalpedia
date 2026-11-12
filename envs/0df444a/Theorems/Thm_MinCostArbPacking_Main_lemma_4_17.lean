-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_17
-- name    : MinCostArbPacking.Main.lemma_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:15.191287+00:00
-- url     : https://prove2.me/theorems/ad3003f9-7643-455f-81e5-71a502aeb597
-- title:
--   Lemma 4.17 — shrinking a cycle of the exchange graph [Sch03, Lemma 41.5α]
-- statement:
--   **Lemma 4.17** ([Sch03, Lemma 41.5α], cited). Let $J$ be common independent in matroids $M_1,M_2$, let $C$ be a cycle of $D_{M_1,M_2}(J)$ and $t\in V(C)$. If $J\oplus V(C)$ is not common independent, then $D_{M_1,M_2}(J)$ has a cycle $C'$ with $V(C')\subsetneq V(C)$ such that
--
--   $$w(C')<0,\qquad\text{or}\qquad w(C')\le w(C)\ \text{ and }\ t\in V(C').$$
--
--   Here $w$ is the total arc weight. The lemma is the exchange step of the proof of the relaxation theorem.
--
--   Differences from the source:
--   - encoding: cycles of $D(J)$ and their vertex sets → duplicate-free lists closing with an arc; `toFinset`; reason: the same objects
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.5, p.20, Lemma 4.17 (cited: Schrijver, Lemma 41.5α)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.17 ([Sch03, Lemma 41.5α]), p.20: let `J` be common independent in `M₁, M₂`, `C` a
cycle of `D_{M₁,M₂}(J)` and `t ∈ V(C)`. If `J ⊕ V(C)` is not common independent, then `D(J)` has a
cycle `C'` with `V(C') ⊊ V(C)` such that `w(C') < 0`, or `w(C') ≤ w(C)` and `t ∈ V(C')`. -/
theorem lemma_4_17 {α : Type} [Fintype α] [DecidableEq α] (M₁ M₂ : Matroid α) (h₁ : M₁.E = Set.univ) (h₂ : M₂.E = Set.univ)
    (c : α → ℝ) (J : Finset α) (hJ : CommonIndep (matInd M₁) (matInd M₂) J) (C : List α)
    (hC : IsCycleE (exArc (matInd M₁) (matInd M₂) J) C) (t : α) (ht : t ∈ C)
    (hnot : ¬ CommonIndep (matInd M₁) (matInd M₂) (symmDiff J C.toFinset)) :
    ∃ C', IsCycleE (exArc (matInd M₁) (matInd M₂) J) C' ∧ C'.toFinset ⊂ C.toFinset ∧
      (cycleWeight c J C' < 0 ∨ (cycleWeight c J C' ≤ cycleWeight c J C ∧ t ∈ C')) := by sorry

end MinCostArbPacking.Main
