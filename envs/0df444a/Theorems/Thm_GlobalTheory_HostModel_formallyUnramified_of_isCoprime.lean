-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_formallyUnramified_of_isCoprime
-- name    : GlobalTheory.HostModel.formallyUnramified_of_isCoprime
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:37.482271+00:00
-- url     : https://prove2.me/theorems/9bf253a7-dd54-41f2-8155-c613270f718d
-- title:
--   Host Model: formally Unramified of is Coprime
-- statement:
--   The Host Model construction uses the formally Unramified of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L36-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/OneAddZeta21PowSevenAddPowFourteenEqZero.lean#L36-L52

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

theorem GlobalTheory.HostModel.formallyUnramified_of_isCoprime {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (σ : B →+* B)
    (hσ : ∀ b, σ (σ b) = b) (hfix : ∀ b, σ b = b → b ∈ Set.range (algebraMap A B)) (w₁ w₂ : B)
    (h : IsCoprime (w₁ - σ w₁) (w₂ - σ w₂)) : Algebra.FormallyUnramified A B := by sorry
