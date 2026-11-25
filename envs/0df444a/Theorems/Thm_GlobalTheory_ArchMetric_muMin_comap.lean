-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_muMin_comap
-- name    : GlobalTheory.ArchMetric.muMin_comap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:46.919828+00:00
-- url     : https://prove2.me/theorems/02fd5f39-3736-4a76-b706-b453b7f286d0
-- title:
--   Arch Metric: mu Min comap
-- statement:
--   The Arch Metric construction uses the mu Min comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1158-L1174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1158-L1174

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
variable (f : V' →ₗ[K] V) (hf : Function.Injective f) {A' : Submodule (𝓞 K) V'}

theorem GlobalTheory.ArchMetric.muMin_comap (hA : A'.FG) :
    (h.comap f hf).muMin A' = h.muMin (A'.map (f.restrictScalars (𝓞 K))) := by sorry
