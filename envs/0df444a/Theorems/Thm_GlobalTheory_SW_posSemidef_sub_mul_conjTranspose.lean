-- Prove2me | Theorems.Thm_GlobalTheory_SW_posSemidef_sub_mul_conjTranspose
-- name    : GlobalTheory.SW.posSemidef_sub_mul_conjTranspose
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:31.92801+00:00
-- url     : https://prove2.me/theorems/b0004e05-8ebc-459f-92ff-65235d4c140c
-- title:
--   SW: pos Semidef sub mul conj Transpose
-- statement:
--   The SW construction uses the pos Semidef sub mul conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubMulConjTranspose.lean#L25-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubMulConjTranspose.lean#L25-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
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
variable {N : ℕ}

theorem GlobalTheory.SW.posSemidef_sub_mul_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) (B : ℝ)
    (hX : ∀ a b, ‖X a b‖ ≤ B) :
    ((((N : ℝ) ^ 2 * B ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ).PosSemidef := by sorry
