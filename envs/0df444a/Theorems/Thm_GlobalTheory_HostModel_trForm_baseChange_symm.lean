-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_trForm_baseChange_symm
-- name    : GlobalTheory.HostModel.trForm_baseChange_symm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:21.982499+00:00
-- url     : https://prove2.me/theorems/c6a9d3c0-6bf8-5465-bef4-48d30f807b1a
-- title:
--   Host Model: tr Form base Change symm
-- statement:
--   The Host Model construction uses the tr Form base Change symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/TrFormBaseChangeNondegenerate.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/TrFormBaseChangeNondegenerate.lean#L123-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_TrFormBaseChangeNondegenerate
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HostModel.trForm_baseChange_symm (H : Host E) (v w : ℝ ⊗[ℤ] 𝓞 E) :
    (trForm H).baseChange ℝ v w = (trForm H).baseChange ℝ w v := by sorry
