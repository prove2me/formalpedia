-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeisH_cols_eq
-- name    : GlobalTheory.SW.HeisH.cols_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:40:32.757834+00:00
-- url     : https://prove2.me/theorems/e724205b-52c6-4a01-a21f-97f22b7da202
-- title:
--   Heis H: cols eq
-- statement:
--   The Heis H construction uses the cols eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L212-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L212-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem GlobalTheory.SW.HeisH.cols_eq {γ : M2 E N} (hγ : γ ∈ UU E N) (d b : Matrix (Fin n) (Fin N) E) :
    d = (fromCols d b * γ⁻¹).toCols₁ * γ.toBlocks₁₁ + (fromCols d b * γ⁻¹).toCols₂ * γ.toBlocks₂₁ ∧
    b = (fromCols d b * γ⁻¹).toCols₁ * γ.toBlocks₁₂ + (fromCols d b * γ⁻¹).toCols₂ * γ.toBlocks₂₂ := by sorry
