-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_unramified_of_isCoprime
-- name    : GlobalTheory.HostModel.unramified_of_isCoprime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:23.462802+00:00
-- url     : https://prove2.me/theorems/122c23ed-9b0a-44a1-ac0d-5d74a7f0b61b
-- title:
--   Host Model: unramified of is Coprime
-- statement:
--   The Host Model construction uses the unramified of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L56-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HostModel.unramified_of_isCoprime (w₁ w₂ : 𝓞 E)
    (h : IsCoprime (w₁ - IsCMField.ringOfIntegersComplexConj E w₁) (w₂ - IsCMField.ringOfIntegersComplexConj E w₂)) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by sorry
