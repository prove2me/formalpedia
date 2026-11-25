-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_comap_gram
-- name    : GlobalTheory.ArchMetric.comap_gram
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:03.755236+00:00
-- url     : https://prove2.me/theorems/27aea0e4-f61c-50d3-a4d1-e1e39b793141
-- title:
--   Arch Metric: comap gram
-- statement:
--   The Arch Metric construction uses the comap gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L422-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L422-L422

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
variable {K : Type*} [Field K] {V V' V'' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
variable (h : ArchMetric K V)
variable (f : V' →ₗ[K] V) (hf : Function.Injective f) (σ : K →+* ℂ)

theorem GlobalTheory.ArchMetric.comap_gram {ι : Type*} (e : ι → V') : (h.comap f hf).gram σ e = h.gram σ (f ∘ e) := by sorry
