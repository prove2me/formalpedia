-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_scale_gramDet
-- name    : GlobalTheory.ArchMetric.scale_gramDet
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:20.671604+00:00
-- url     : https://prove2.me/theorems/7ad8b41e-0cf3-4365-9ebe-5fdfed33db1b
-- title:
--   Arch Metric: scale gram Det
-- statement:
--   The Arch Metric construction uses the scale gram Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L477-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L477-L479

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

theorem GlobalTheory.ArchMetric.scale_gramDet {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V) :
    (h.scale c hc).gramDet σ e = c σ ^ Fintype.card ι * h.gramDet σ e := by sorry
