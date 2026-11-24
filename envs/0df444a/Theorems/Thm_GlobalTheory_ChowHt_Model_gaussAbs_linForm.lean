-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_Model_gaussAbs_linForm
-- name    : GlobalTheory.ChowHt.Model.gaussAbs_linForm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:53.969797+00:00
-- url     : https://prove2.me/theorems/4ba8abb7-90ff-4dd9-86d8-15a8eb52b9cf
-- title:
--   Model: gauss Abs lin Form
-- statement:
--   The Model construction uses the gauss Abs lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L66-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BlockSphereMeanLinForm.lean#L66-L93

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

theorem GlobalTheory.ChowHt.Model.gaussAbs_linForm {F : Type} [Field F] [NumberField F] {N : ℕ} (v : FinitePlace F)
    (c : Fin N → F) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linForm c) = ⨆ k, v (c k) := by sorry
