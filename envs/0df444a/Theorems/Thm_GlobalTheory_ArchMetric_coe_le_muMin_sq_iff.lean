-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_coe_le_muMin_sq_iff
-- name    : GlobalTheory.ArchMetric.coe_le_muMin_sq_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:33.23571+00:00
-- url     : https://prove2.me/theorems/c1098c7f-5b0b-5ff7-a945-73af94fc25e5
-- title:
--   Arch Metric: coe le mu Min sq iff
-- statement:
--   The Arch Metric construction uses the coe le mu Min sq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1200-L1206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1200-L1206

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

theorem GlobalTheory.ArchMetric.coe_le_muMin_sq_iff {c : ℝ} : (c : EReal) ≤ h.muMin_sq A ↔ ∀ W : Submodule K V,
    ¬ A ≤ W.restrictScalars (𝓞 K) → c ≤ 2 * h.quotSlope A (A ⊓ W.restrictScalars (𝓞 K)) := by sorry
