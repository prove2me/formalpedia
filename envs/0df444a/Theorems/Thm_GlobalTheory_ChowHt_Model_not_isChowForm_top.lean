-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_Model_not_isChowForm_top
-- name    : GlobalTheory.ChowHt.Model.not_isChowForm_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:54.093446+00:00
-- url     : https://prove2.me/theorems/8d21ccfd-d0d9-434a-80db-d777fb3f3478
-- title:
--   Model: not is Chow Form top
-- statement:
--   The Model construction uses the not is Chow Form top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L166-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L166-L181

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

theorem GlobalTheory.ChowHt.Model.not_isChowForm_top {k : Type} [Field k] {N D δ : ℕ}
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : ¬ IsChowForm (⊤ : Ideal (MvPolynomial (Fin N) k)) D δ f := by sorry
