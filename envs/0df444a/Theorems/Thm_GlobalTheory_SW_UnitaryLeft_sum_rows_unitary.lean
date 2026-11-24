-- Prove2me | Theorems.Thm_GlobalTheory_SW_UnitaryLeft_sum_rows_unitary
-- name    : GlobalTheory.SW.UnitaryLeft.sum_rows_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:19.337804+00:00
-- url     : https://prove2.me/theorems/793c31ec-a9d7-4407-b183-5667ff1cfe2d
-- title:
--   Unitary Left: sum rows unitary
-- statement:
--   The Unitary Left construction uses the sum rows unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L22-L27

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

theorem GlobalTheory.SW.UnitaryLeft.sum_rows_unitary {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : Qᵀ * P = 1)
    (U V : Matrix (Fin n) (Fin N) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ∑ k, (P * U) k ⬝ᵥ A *ᵥ (Q * V) k = ∑ k, U k ⬝ᵥ A *ᵥ V k := by sorry
