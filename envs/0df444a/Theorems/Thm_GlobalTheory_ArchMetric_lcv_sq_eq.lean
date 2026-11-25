-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_lcv_sq_eq
-- name    : GlobalTheory.ArchMetric.lcv_sq_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:07.262302+00:00
-- url     : https://prove2.me/theorems/554bb6cb-8e90-4bd4-b423-98df34f702c1
-- title:
--   Arch Metric: lcv sq eq
-- statement:
--   The Arch Metric construction uses the lcv sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L999-L1005
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L999-L1005

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

theorem GlobalTheory.ArchMetric.lcv_sq_eq (hA : A.FG) {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → V}
    (he : IsLatticeFrame A e) :
    h.lcv_sq A = (∑ σ : K →+* ℂ, Real.log (h.gramDet σ e)) / finrank ℚ K -
      2 / finrank ℚ K *
        Real.log (Nat.card (A ⧸ (Submodule.span (𝓞 K) (Set.range e)).submoduleOf A)) := by sorry
