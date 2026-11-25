-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_unramified_of_sqrt
-- name    : GlobalTheory.HostModel.unramified_of_sqrt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:34.923682+00:00
-- url     : https://prove2.me/theorems/d7f27d4f-8d44-4cb3-9318-9b9a9ded7dcb
-- title:
--   Host Model: unramified of sqrt
-- statement:
--   The Host Model construction uses the unramified of sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L103-L109

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

theorem GlobalTheory.HostModel.unramified_of_sqrt {x₁ x₂ w₁ w₂ : 𝓞 E} {m n : ℕ} (hmn : m.Coprime n) (h₁ : x₁ ^ 2 = -(m : 𝓞 E))
    (h₂ : x₂ ^ 2 = -(n : 𝓞 E)) (hw₁ : 2 * w₁ = 1 + x₁) (hw₂ : 2 * w₂ = 1 + x₂) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by sorry
