-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_scaleNormExp_norm
-- name    : GlobalTheory.ArchMetric.scaleNormExp_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:20.410944+00:00
-- url     : https://prove2.me/theorems/37b3cb98-e1cd-46c4-8bbe-d1798c0faf9a
-- title:
--   Arch Metric: scale Norm Exp norm
-- statement:
--   The Arch Metric construction uses the scale Norm Exp norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L492-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L492-L494

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

theorem GlobalTheory.ArchMetric.scaleNormExp_norm (t : (K →+* ℂ) → ℝ) (σ : K →+* ℂ) (x : V) :
    (h.scaleNormExp t).norm σ x = Real.exp (t σ) * h.norm σ x := by sorry
