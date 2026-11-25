-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_hypDatum_EF_inr_inr
-- name    : GlobalTheory.HostModel.hypDatum_EF_inr_inr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:35.533301+00:00
-- url     : https://prove2.me/theorems/6a3aa3c3-3947-5f6c-9cb1-7fbdf5e8fa9f
-- title:
--   Host Model: hyp Datum EF inr inr
-- statement:
--   The Host Model construction uses the hyp Datum EF inr inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ToMatrixTrFormBaseChange.lean#L383-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ToMatrixTrFormBaseChange.lean#L383-L383

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ConjDual

theorem GlobalTheory.HostModel.hypDatum_EF_inr_inr (H : Host E) (f g : ConjDual H) : (hypDatum H).EF (0, f) (0, g) = 0 := by sorry
