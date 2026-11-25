-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_norm_add_sq
-- name    : GlobalTheory.ArchMetric.norm_add_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:57:36.834574+00:00
-- url     : https://prove2.me/theorems/6542893a-bb7b-42a9-b40d-cfac39b64e87
-- title:
--   Arch Metric: norm add sq
-- statement:
--   The Arch Metric construction uses the norm add sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L387-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L387-L391

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

theorem GlobalTheory.ArchMetric.norm_add_sq (σ : K →+* ℂ) (x y : V) :
    h.norm σ (x + y) ^ 2 = h.norm σ x ^ 2 + 2 * (h.form σ x y).re + h.norm σ y ^ 2 := by sorry
