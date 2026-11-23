-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayData_mem_principalRay_iff
-- name    : GlobalTheory.Mem.RayData.mem_principalRay_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:30.263796+00:00
-- url     : https://prove2.me/theorems/90e71c28-0800-4a8d-8bc5-c328101cf71d
-- title:
--   Ray Data: mem principal Ray iff
-- statement:
--   The Ray Data construction uses the mem principal Ray iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L62-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean#L62-L103

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

theorem GlobalTheory.Mem.RayData.mem_principalRay_iff (𝔮 : Ideal (𝓞 K)) (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    x ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 ↔ ∃ (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0), a - 1 ∈ 𝔮 ∧ b - 1 ∈ 𝔮 ∧
      x * _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) := by sorry
