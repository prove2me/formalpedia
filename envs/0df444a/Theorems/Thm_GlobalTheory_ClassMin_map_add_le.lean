-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_map_add_le
-- name    : GlobalTheory.ClassMin.map_add_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:07.138717+00:00
-- url     : https://prove2.me/theorems/152e661f-f61e-4799-b0ef-2b010a9f27b0
-- title:
--   Class Min: map add le
-- statement:
--   The Class Min construction uses the map add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L86-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}

theorem GlobalTheory.ClassMin.map_add_le (hQ : ∀ x, 0 ≤ Q x) {j : ℤ} (hj : 1 ≤ j) (a b : X) :
    Q (a + b) ≤ (1 + 1 / j) * Q a + (1 + j) * Q b := by sorry
