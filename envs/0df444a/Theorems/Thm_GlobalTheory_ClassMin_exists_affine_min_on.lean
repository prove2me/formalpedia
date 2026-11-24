-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_exists_affine_min_on
-- name    : GlobalTheory.ClassMin.exists_affine_min_on
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:46.70898+00:00
-- url     : https://prove2.me/theorems/4b888f81-75ac-4797-969a-7b032e13baa5
-- title:
--   Class Min: exists affine min on
-- statement:
--   The Class Min construction uses the exists affine min on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L346-L348

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
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ}

theorem GlobalTheory.ClassMin.exists_affine_min_on (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ)
    {S : Set X} (hS : S.Nonempty) : ∃ a ∈ S, ∀ x ∈ S, t * Q a + ν a ≤ t * Q x + ν x := by sorry
