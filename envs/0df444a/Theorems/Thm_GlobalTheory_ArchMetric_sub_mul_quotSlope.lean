-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_sub_mul_quotSlope
-- name    : GlobalTheory.ArchMetric.sub_mul_quotSlope
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:19.146814+00:00
-- url     : https://prove2.me/theorems/0f1273d4-b6a5-4e79-a4e6-521ea1626814
-- title:
--   Arch Metric: sub mul quot Slope
-- statement:
--   The Arch Metric construction uses the sub mul quot Slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1029-L1034
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1029-L1034

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

theorem GlobalTheory.ArchMetric.sub_mul_quotSlope (hA : A.FG) {W : Submodule K V} (hW : ¬ A ≤ W.restrictScalars (𝓞 K)) :
    ((finrank (𝓞 K) A : ℝ) -
        finrank (𝓞 K) (A ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V)) *
      h.quotSlope A (A ⊓ W.restrictScalars (𝓞 K)) =
      h.degNorm A - h.degNorm (A ⊓ W.restrictScalars (𝓞 K)) := by sorry
