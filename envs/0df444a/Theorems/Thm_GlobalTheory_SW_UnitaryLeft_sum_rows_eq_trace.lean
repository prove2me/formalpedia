-- Prove2me | Theorems.Thm_GlobalTheory_SW_UnitaryLeft_sum_rows_eq_trace
-- name    : GlobalTheory.SW.UnitaryLeft.sum_rows_eq_trace
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:45:34.052925+00:00
-- url     : https://prove2.me/theorems/bce1277b-f9a8-4843-9d7b-d2414c8e62e2
-- title:
--   Unitary Left: sum rows eq trace
-- statement:
--   The Unitary Left construction uses the sum rows eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean#L14-L20

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

theorem GlobalTheory.SW.UnitaryLeft.sum_rows_eq_trace {n N : ℕ} (U V : Matrix (Fin n) (Fin N) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ∑ k, U k ⬝ᵥ A *ᵥ V k = (U * A * Vᵀ).trace := by sorry
