-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_tendsto_affine_cofinite
-- name    : GlobalTheory.ClassMin.tendsto_affine_cofinite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:13:37.189042+00:00
-- url     : https://prove2.me/theorems/f7ba21c8-4dad-4922-b2b7-fefed6faa7be
-- title:
--   Class Min: tendsto affine cofinite
-- statement:
--   The Class Min construction uses the tendsto affine cofinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L341-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L341-L344

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

theorem GlobalTheory.ClassMin.tendsto_affine_cofinite (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t)
    (ν : X →+ ℝ) : Tendsto (fun x => t * Q x + ν x) cofinite atTop := by sorry
