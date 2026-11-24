-- Prove2me | Theorems.Thm_GlobalTheory_SW_UnitaryLeft_thH_mul
-- name    : GlobalTheory.SW.UnitaryLeft.thH_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:18.275462+00:00
-- url     : https://prove2.me/theorems/67e9a7e4-566c-49e7-bd07-b30b3140b8c7
-- title:
--   Unitary Left: th H mul
-- statement:
--   The Unitary Left construction uses the th H mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L73-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L73-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UnitaryLeft
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem GlobalTheory.SW.UnitaryLeft.thH_mul {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) Z z z' = thH Ψ φ Z (mv Ψ h z) (mv' Ψ h z') := by sorry
