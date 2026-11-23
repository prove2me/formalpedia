-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCharMult_sp_rel_transpose
-- name    : GlobalTheory.ThetaCharMult.sp_rel_transpose
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:08.58471+00:00
-- url     : https://prove2.me/theorems/e6e47310-3400-43e7-aac0-a02a0492059b
-- title:
--   Theta Char Mult: sp rel transpose
-- statement:
--   The Theta Char Mult construction uses the sp rel transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaSqLawOfZero.lean#L14-L19

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

theorem GlobalTheory.ThetaCharMult.sp_rel_transpose {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    ((cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ = -1) ∧
    ((cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₂₂ᵀ = 0) := by sorry
