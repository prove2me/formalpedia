-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCharMult_phase_dvd
-- name    : GlobalTheory.ThetaCharMult.phase_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:04:31.663857+00:00
-- url     : https://prove2.me/theorems/d26dbcd1-ea1b-4473-aae0-3da851cd4555
-- title:
--   Theta Char Mult: phase dvd
-- statement:
--   The Theta Char Mult construction uses the phase dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L102-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L102-L116

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

theorem GlobalTheory.ThetaCharMult.phase_dvd {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j) (hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j)
    (n n' : Fin g → ℤ) :
    (8 : ℤ) ∣ n ⬝ᵥ n' - (γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n') ⬝ᵥ
      (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n') := by sorry
