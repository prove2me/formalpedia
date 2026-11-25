-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_muMax_sq_le_coe_iff
-- name    : GlobalTheory.ArchMetric.muMax_sq_le_coe_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:56:37.952739+00:00
-- url     : https://prove2.me/theorems/0360a336-5b70-5517-b6f6-f8f1c1394bb2
-- title:
--   Arch Metric: mu Max sq le coe iff
-- statement:
--   The Arch Metric construction uses the mu Max sq le coe iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1184-L1190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L1184-L1190

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

theorem GlobalTheory.ArchMetric.muMax_sq_le_coe_iff {c : ℝ} :
    h.muMax_sq A ≤ c ↔ ∀ B ≤ A, B ≠ ⊥ → h.slope_sq B ≤ c := by sorry
