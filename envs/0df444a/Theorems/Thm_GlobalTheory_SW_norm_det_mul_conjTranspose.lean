-- Prove2me | Theorems.Thm_GlobalTheory_SW_norm_det_mul_conjTranspose
-- name    : GlobalTheory.SW.norm_det_mul_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:28.961132+00:00
-- url     : https://prove2.me/theorems/f926c254-db7e-48dd-9ca7-0de92c8999b7
-- title:
--   SW: norm det mul conj Transpose
-- statement:
--   The SW construction uses the norm det mul conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubMulConjTranspose.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubMulConjTranspose.lean#L68-L71

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

theorem GlobalTheory.SW.norm_det_mul_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) :
    (A * Aᴴ).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by sorry
