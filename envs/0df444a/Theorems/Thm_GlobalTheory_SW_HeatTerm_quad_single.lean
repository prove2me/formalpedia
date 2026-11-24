-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeatTerm_quad_single
-- name    : GlobalTheory.SW.HeatTerm.quad_single
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:40:55.435103+00:00
-- url     : https://prove2.me/theorems/669b8539-12ef-4f11-af33-91484e9b782f
-- title:
--   Heat Term: quad single
-- statement:
--   The Heat Term construction uses the quad single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L64-L68

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

theorem GlobalTheory.SW.HeatTerm.quad_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (u v : Fin N → ℂ) :
    u ⬝ᵥ (S * Matrix.single a b 1 * S) *ᵥ v = (u ᵥ* S) a * (S *ᵥ v) b := by sorry
