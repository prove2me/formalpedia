-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_Model_isChowForm_point
-- name    : GlobalTheory.ChowHt.Model.isChowForm_point
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:06.233844+00:00
-- url     : https://prove2.me/theorems/3743fe2e-39de-4c7b-8b5f-4c032875f658
-- title:
--   Model: is Chow Form point
-- statement:
--   The Model construction uses the is Chow Form point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L11-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model

theorem GlobalTheory.ChowHt.Model.isChowForm_point (k : Type) [Field k] :
    IsChowForm (Ideal.span {(X 1 : MvPolynomial (Fin 2) k)}) 0 1 (X (0, 0)) := by sorry
