-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_arDeg_eq_of_span_eq
-- name    : GlobalTheory.ArchMetric.arDeg_eq_of_span_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:57.040006+00:00
-- url     : https://prove2.me/theorems/7e4770fc-7608-4dab-9e2a-00a4b0566cd0
-- title:
--   Arch Metric: ar Deg eq of span eq
-- statement:
--   The Arch Metric construction uses the ar Deg eq of span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L898-L907
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L898-L907

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
variable {A : Submodule (𝓞 K) V} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.ArchMetric.arDeg_eq_of_span_eq (hA : A.FG) {e : ι → V} (he : LinearIndependent K e)
    (hs : Submodule.span K (Set.range e) = Submodule.span K (A : Set V)) :
    h.arDeg A =
      Real.log ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex A.toAddSubgroup) -
        Real.log (A.toAddSubgroup.relIndex (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup) -
        ∑ σ : K →+* ℂ, 1 / 2 * Real.log (h.gramDet σ e) := by sorry
