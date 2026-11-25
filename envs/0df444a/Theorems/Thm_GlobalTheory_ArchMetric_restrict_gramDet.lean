-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_restrict_gramDet
-- name    : GlobalTheory.ArchMetric.restrict_gramDet
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:56:22.297033+00:00
-- url     : https://prove2.me/theorems/cb6635be-d88b-4d27-8c53-7c1a28173fe2
-- title:
--   Arch Metric: restrict gram Det
-- statement:
--   The Arch Metric construction uses the restrict gram Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L450-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L450-L452

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

theorem GlobalTheory.ArchMetric.restrict_gramDet (W : Submodule K V) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : ι → W) :
    (h.restrict W).gramDet σ e = h.gramDet σ fun i => (e i : V) := by sorry
