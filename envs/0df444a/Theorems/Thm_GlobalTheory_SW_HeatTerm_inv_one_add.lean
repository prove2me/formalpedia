-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeatTerm_inv_one_add
-- name    : GlobalTheory.SW.HeatTerm.inv_one_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:40:04.629364+00:00
-- url     : https://prove2.me/theorems/ae6cf6b0-c884-4f06-877b-447d2ec96ea4
-- title:
--   Heat Term: inv one add
-- statement:
--   The Heat Term construction uses the inv one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L47-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L47-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section

theorem GlobalTheory.SW.HeatTerm.inv_one_add {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (s : ℂ)
    (h : 1 + s * S b a ≠ 0) :
    (1 + S * Matrix.single a b s)⁻¹ = 1 - (s / (1 + s * S b a)) • (S * Matrix.single a b 1) := by sorry
