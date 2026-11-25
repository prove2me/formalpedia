-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_arDeg_sub_arDeg_of_span_eq
-- name    : GlobalTheory.ArchMetric.arDeg_sub_arDeg_of_span_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:57:09.262825+00:00
-- url     : https://prove2.me/theorems/40703784-f549-5417-9713-c05b8840d6ae
-- title:
--   Arch Metric: ar Deg sub ar Deg of span eq
-- statement:
--   The Arch Metric construction uses the ar Deg sub ar Deg of span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L883-L896
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L883-L896

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

theorem GlobalTheory.ArchMetric.arDeg_sub_arDeg_of_span_eq {B : Submodule (𝓞 K) V} (hA : A.FG) (hB : B.FG)
    (hAB : Submodule.span K (A : Set V) = Submodule.span K (B : Set V)) :
    h.arDeg A - h.arDeg B = Real.log (B.toAddSubgroup.relIndex A.toAddSubgroup) -
      Real.log (A.toAddSubgroup.relIndex B.toAddSubgroup) := by sorry
