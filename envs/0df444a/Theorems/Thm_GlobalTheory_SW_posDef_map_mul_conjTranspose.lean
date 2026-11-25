-- Prove2me | Theorems.Thm_GlobalTheory_SW_posDef_map_mul_conjTranspose
-- name    : GlobalTheory.SW.posDef_map_mul_conjTranspose
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:26.675175+00:00
-- url     : https://prove2.me/theorems/e450649a-cdd7-479d-89bd-e438f0c87648
-- title:
--   SW: pos Def map mul conj Transpose
-- statement:
--   The SW construction uses the pos Def map mul conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L121-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
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
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.posDef_map_mul_conjTranspose {E m n : Type} [Field E] [Fintype m] [Fintype n]
    {W : Matrix n m E} (hW : LinearIndependent E fun i => W i) (σ : E →+* ℂ) :
    (W.map σ * (W.map σ)ᴴ).PosDef := by sorry
