-- Prove2me | Theorems.Thm_GlobalTheory_two_dvd_of_entire_sign_periodic
-- name    : GlobalTheory.two_dvd_of_entire_sign_periodic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:48:11.946547+00:00
-- url     : https://prove2.me/theorems/8c1002b4-df7b-4265-9a09-09ca44a054a2
-- title:
--   Global Theory: two dvd of entire sign periodic
-- statement:
--   The Global Theory construction uses the two dvd of entire sign periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TwoDvdMultiplierOfThetaZActEqUnitMul.lean#L75-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TwoDvdMultiplierOfThetaZActEqUnitMul.lean#L75-L106

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

theorem GlobalTheory.two_dvd_of_entire_sign_periodic {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) {σ : (Fin g → ℂ) → ℂ} (hσ : Differentiable ℂ σ) (h0 : σ 0 ≠ 0)
    {N : (Fin g → ℤ) → (Fin g → ℤ) → ℤ}
    (h : ∀ m m' z, σ (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec m + _root_.ReciprocityTheory.PTheta.ofIntVec m') = _root_.ReciprocityTheory.PTheta.eC ((N m m' : ℂ) / 2) * σ z)
    (m m' : Fin g → ℤ) : 2 ∣ N m m' := by sorry
