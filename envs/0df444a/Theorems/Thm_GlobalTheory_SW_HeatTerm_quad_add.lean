-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeatTerm_quad_add
-- name    : GlobalTheory.SW.HeatTerm.quad_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:40:20.58925+00:00
-- url     : https://prove2.me/theorems/bfad4a33-7f59-483c-9717-739834824143
-- title:
--   Heat Term: quad add
-- statement:
--   The Heat Term construction uses the quad add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L116-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean#L116-L140

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

theorem GlobalTheory.SW.HeatTerm.quad_add {n N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (k : Fin n) (a b : Fin N) (s t : ℂ) :
    ∑ j, (z' + Matrix.single k b t) j ⬝ᵥ S *ᵥ (z + Matrix.single k a s) j =
      ∑ j, z' j ⬝ᵥ S *ᵥ z j + s * (z' k ᵥ* S) a + t * ((S *ᵥ z k) b + s * S b a) := by sorry
