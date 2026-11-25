-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_hypDatum_EF
-- name    : GlobalTheory.HostModel.hypDatum_EF
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:07:49.759377+00:00
-- url     : https://prove2.me/theorems/5063e877-17e7-4c6f-9159-474079415b22
-- title:
--   Host Model: hyp Datum EF
-- statement:
--   The Host Model construction uses the hyp Datum EF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ToMatrixTrFormBaseChange.lean#L375-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ToMatrixTrFormBaseChange.lean#L375-L376

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

theorem GlobalTheory.HostModel.hypDatum_EF (H : Host E) (x y : 𝓞 E) (f g : ConjDual H) :
    (hypDatum H).EF (x, f) (y, g) = toDual H f y - toDual H g x := by sorry
