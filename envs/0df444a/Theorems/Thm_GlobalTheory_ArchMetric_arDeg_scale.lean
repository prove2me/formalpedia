-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_arDeg_scale
-- name    : GlobalTheory.ArchMetric.arDeg_scale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:28.758616+00:00
-- url     : https://prove2.me/theorems/156422f7-53cd-4192-b6b7-f1b4043da1c3
-- title:
--   Arch Metric: ar Deg scale
-- statement:
--   The Arch Metric construction uses the ar Deg scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L926-L937
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L926-L937

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

theorem GlobalTheory.ArchMetric.arDeg_scale (c : (K →+* ℂ) → ℝ) (hc : ∀ σ, 0 < c σ) (hA : A.FG) :
    (h.scale c hc).arDeg A =
      h.arDeg A - finrank (𝓞 K) A / 2 * ∑ σ : K →+* ℂ, Real.log (c σ) := by sorry
