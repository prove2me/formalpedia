-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_ConjInvariant_norm_conjugate
-- name    : GlobalTheory.ArchMetric.ConjInvariant.norm_conjugate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:47.841647+00:00
-- url     : https://prove2.me/theorems/4b8f6bf9-4c45-40d9-b292-843539c1c441
-- title:
--   Conj Invariant: norm conjugate
-- statement:
--   The Conj Invariant construction uses the norm conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L401-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L401-L403

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
variable {h}

theorem GlobalTheory.ArchMetric.ConjInvariant.norm_conjugate (hc : h.ConjInvariant) (σ : K →+* ℂ) (x : V) :
    h.norm (ComplexEmbedding.conjugate σ) x = h.norm σ x := by sorry
