-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChange_change_of_normalisation
-- name    : GlobalTheory.PeriodChange.change_of_normalisation
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:26.205484+00:00
-- url     : https://prove2.me/theorems/852555a6-5eac-4981-9ffa-397b1d73281e
-- title:
--   Period Change: change of normalisation
-- statement:
--   The Period Change construction uses the change of normalisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ChangeOfNormalisation.lean#L59-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ChangeOfNormalisation.lean#L59-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ChangeOfNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChange
open Complex Matrix NumberField

theorem GlobalTheory.PeriodChange.change_of_normalisation {g : ℕ} (h h' τ' A B L R : Matrix (Fin g) (Fin g) ℂ)
    (hA : h * L = A) (hB : h * R = B) (hL : h' * L = 1) (hR : h' * R = τ') (hs : τ'.IsSymm)
    (hu : IsUnit h.det) :
    τ' = Bᵀ * (Aᵀ)⁻¹ ∧ h' = ((Aᵀ)⁻¹)ᵀ * h ∧ h.det = (Aᵀ).det * h'.det := by sorry
