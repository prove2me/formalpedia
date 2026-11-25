-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_comap_gramDet
-- name    : GlobalTheory.ArchMetric.comap_gramDet
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:43.965575+00:00
-- url     : https://prove2.me/theorems/1c0148e5-8bf8-4778-b06c-de3b96cf18a8
-- title:
--   Arch Metric: comap gram Det
-- statement:
--   The Arch Metric construction uses the comap gram Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L424-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L424-L425

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

theorem GlobalTheory.ArchMetric.comap_gramDet {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V') :
    (h.comap f hf).gramDet σ e = h.gramDet σ (f ∘ e) := by sorry
