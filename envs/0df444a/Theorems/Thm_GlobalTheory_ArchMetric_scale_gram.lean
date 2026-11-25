-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_scale_gram
-- name    : GlobalTheory.ArchMetric.scale_gram
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:56:44.788242+00:00
-- url     : https://prove2.me/theorems/da5aca4e-d35a-5274-bfab-26dfaafdeba6
-- title:
--   Arch Metric: scale gram
-- statement:
--   The Arch Metric construction uses the scale gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L474-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L474-L475

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
variable (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) (σ : K →+* ℂ)

theorem GlobalTheory.ArchMetric.scale_gram {ι : Type*} (e : ι → V) :
    (h.scale c hc).gram σ e = (c σ : ℂ) • h.gram σ e := by sorry
