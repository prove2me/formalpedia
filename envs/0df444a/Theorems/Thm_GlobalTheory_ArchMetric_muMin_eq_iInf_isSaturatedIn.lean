-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_muMin_eq_iInf_isSaturatedIn
-- name    : GlobalTheory.ArchMetric.muMin_eq_iInf_isSaturatedIn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:10.070439+00:00
-- url     : https://prove2.me/theorems/e5bc0bfb-7353-5c69-be2c-43adda9d07df
-- title:
--   Arch Metric: mu Min eq i Inf is Saturated In
-- statement:
--   The Arch Metric construction uses the mu Min eq i Inf is Saturated In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1074-L1082
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1074-L1082

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped ComplexOrder ComplexConjugate
open GlobalTheory
open GlobalTheory.ArchMetric
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : ArchMetric K V)
variable {A B : Submodule (𝓞 K) V}

theorem GlobalTheory.ArchMetric.muMin_eq_iInf_isSaturatedIn (A : Submodule (𝓞 K) V) :
    h.muMin A = ⨅ (B : Submodule (𝓞 K) V) (_ : IsSaturatedIn A B) (_ : B ≠ A),
      (h.quotSlope A B : EReal) := by sorry
