-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_coe_idealUnit
-- name    : GlobalTheory.Mem.RayData.coe_idealUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:27.572215+00:00
-- url     : https://prove2.me/theorems/4aded40a-4a4a-4a07-8634-4b1647fb3060
-- title:
--   Ray Data: coe ideal Unit
-- statement:
--   The Ray Data construction uses the coe ideal Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L20-L21

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

theorem GlobalTheory.Mem.RayData.coe_idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (idealUnit I hI : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) := by sorry
