-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_conjInvariant_diag
-- name    : GlobalTheory.ArchMetric.conjInvariant_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:57:15.799019+00:00
-- url     : https://prove2.me/theorems/4c2015db-21a4-5b55-98af-0603afb7cbc6
-- title:
--   Arch Metric: conj Invariant diag
-- statement:
--   The Arch Metric construction uses the conj Invariant diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L194-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L194-L197

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

theorem GlobalTheory.ArchMetric.conjInvariant_diag {ι : Type*} [Fintype ι] {d : (K →+* ℂ) → ι → ℝ}
    (hd : ∀ σ i, 0 < d σ i) (hc : ∀ σ, d (ComplexEmbedding.conjugate σ) = d σ) :
    (diag d hd).ConjInvariant := by sorry
