-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_conjInvariant_ofGram
-- name    : GlobalTheory.ArchMetric.conjInvariant_ofGram
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:02.214044+00:00
-- url     : https://prove2.me/theorems/4e2e03eb-bbdb-53bb-8351-f60a99bba4ad
-- title:
--   Arch Metric: conj Invariant of Gram
-- statement:
--   The Arch Metric construction uses the conj Invariant of Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L199-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L199-L203

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

theorem GlobalTheory.ArchMetric.conjInvariant_ofGram {ι : Type*} [Fintype ι] (b : Basis ι K V)
    {G : (K →+* ℂ) → Matrix ι ι ℂ} (hG : ∀ σ, (G σ).PosDef)
    (hc : ∀ σ i j, G (ComplexEmbedding.conjugate σ) i j = conj (G σ i j)) :
    (ofGram b G hG).ConjInvariant := by sorry
