-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCharMult_dvd_dot_right
-- name    : GlobalTheory.ThetaCharMult.dvd_dot_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:56.083973+00:00
-- url     : https://prove2.me/theorems/b3808b51-ccd9-4083-bf34-81bc2d40b1b7
-- title:
--   Theta Char Mult: dvd dot right
-- statement:
--   The Theta Char Mult construction uses the dvd dot right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L99-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaCharMult
variable {g : ℕ}

theorem GlobalTheory.ThetaCharMult.dvd_dot_right {k : ℤ} {v : Fin g → ℤ} (h : ∀ i, k ∣ v i) (u : Fin g → ℤ) : k ∣ u ⬝ᵥ v := by sorry
