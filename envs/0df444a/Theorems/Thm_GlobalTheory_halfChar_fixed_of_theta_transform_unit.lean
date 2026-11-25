-- Prove2me | Theorems.Thm_GlobalTheory_halfChar_fixed_of_theta_transform_unit
-- name    : GlobalTheory.halfChar_fixed_of_theta_transform_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:50.68446+00:00
-- url     : https://prove2.me/theorems/e78d204b-ed71-5051-9c0f-5c82420a3316
-- title:
--   Global Theory: half Char fixed of theta transform unit
-- statement:
--   The Global Theory construction uses the half Char fixed of theta transform unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TwoDvdMultiplierOfThetaZActEqUnitMul.lean#L165-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TwoDvdMultiplierOfThetaZActEqUnitMul.lean#L165-L336

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
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
noncomputable section
open GlobalTheory
open Complex Matrix NumberField Filter Topology

theorem GlobalTheory.halfChar_fixed_of_theta_transform_unit :
    ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → ∀ (c : ℂ) (n n' : Fin g → ℤ), c ≠ 0 → (∀ τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g), ∀ z : Fin g → ℂ, _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.zAct γ τ z) (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ) ^ 2 = c * (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det * _root_.ReciprocityTheory.PTheta.eC (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.expArg γ τ z) * _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec 0) z τ ^ 2) → ∀ τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g), ∀ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → (∀ z, _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n') (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.zAct γ τ z) (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ) = ρ z * _root_.ReciprocityTheory.PTheta.theta (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n) (_root_.ReciprocityTheory.ChartRestriction.G.Key.halfVec n') z τ) → (∀ i, (2 : ℤ) ∣ (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i) ∧ (∀ i, (2 : ℤ) ∣ (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i) := by sorry
