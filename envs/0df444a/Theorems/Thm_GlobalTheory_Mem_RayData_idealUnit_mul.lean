-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_idealUnit_mul
-- name    : GlobalTheory.Mem.RayData.idealUnit_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.812962+00:00
-- url     : https://prove2.me/theorems/7874cf47-a989-4060-b402-8ed6920e69b5
-- title:
--   Ray Data: ideal Unit mul
-- statement:
--   The Ray Data construction uses the ideal Unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L32-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayData
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Mem.RayData.idealUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : I * J ≠ ⊥) :
    _root_.GlobalTheory.Mem.RayData.idealUnit (I * J) h = _root_.GlobalTheory.Mem.RayData.idealUnit I hI * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ := by sorry
