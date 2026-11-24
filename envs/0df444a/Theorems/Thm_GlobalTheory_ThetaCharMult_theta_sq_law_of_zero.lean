-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCharMult_theta_sq_law_of_zero
-- name    : GlobalTheory.ThetaCharMult.theta_sq_law_of_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:31.563446+00:00
-- url     : https://prove2.me/theorems/9c1086d3-0e15-4c31-9ac2-18af852e81e5
-- title:
--   Theta Char Mult: theta sq law of zero
-- statement:
--   The Theta Char Mult construction uses the theta sq law of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L137-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L137-L178

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

theorem GlobalTheory.ThetaCharMult.theta_sq_law_of_zero : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → ∀ (c : ℂ) (n n' : Fin g → ℤ), (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → (∀ i, (2 : ℤ) ∣ (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i) ∧ (∀ i, (2 : ℤ) ∣ (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2) := by sorry
