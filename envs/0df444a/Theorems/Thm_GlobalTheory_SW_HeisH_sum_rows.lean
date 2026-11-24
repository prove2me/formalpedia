-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeisH_sum_rows
-- name    : GlobalTheory.SW.HeisH.sum_rows
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:40:41.993817+00:00
-- url     : https://prove2.me/theorems/4e3db35c-2110-4c08-92f5-f4cdab5e13ba
-- title:
--   Heis H: sum rows
-- statement:
--   The Heis H construction uses the sum rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L109-L112

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
variable {n N : ℕ}

theorem GlobalTheory.SW.HeisH.sum_rows (K : Matrix (Fin N) (Fin N) ℂ) (z w : Matrix (Fin n) (Fin N) ℂ) :
    ∑ k, w k ⬝ᵥ K *ᵥ z k = (w * K * zᵀ).trace := by sorry
