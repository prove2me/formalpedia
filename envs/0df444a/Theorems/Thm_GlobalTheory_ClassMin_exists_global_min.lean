-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_exists_global_min
-- name    : GlobalTheory.ClassMin.exists_global_min
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:00.160871+00:00
-- url     : https://prove2.me/theorems/f6c2dfe4-3165-4cf0-b709-d8c3f7a41afc
-- title:
--   Class Min: exists global min
-- statement:
--   The Class Min construction uses the exists global min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L350-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L350-L352

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

theorem GlobalTheory.ClassMin.exists_global_min (hQ : (realExtension Q).PosDef) (ν : X →+ ℝ) {N : ℝ} (hN : 0 < N) :
    ∃ a, ∀ x, Q a / N + ν a ≤ Q x / N + ν x := by sorry
