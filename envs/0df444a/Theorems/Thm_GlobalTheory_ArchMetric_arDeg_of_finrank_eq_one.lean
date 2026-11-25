-- Prove2me | Theorems.Thm_GlobalTheory_ArchMetric_arDeg_of_finrank_eq_one
-- name    : GlobalTheory.ArchMetric.arDeg_of_finrank_eq_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:49.194773+00:00
-- url     : https://prove2.me/theorems/dfdf8c96-4002-4947-a653-270aba0cbf2a
-- title:
--   Arch Metric: ar Deg of finrank eq one
-- statement:
--   The Arch Metric construction uses the ar Deg of finrank eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L850-L862
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L850-L862

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

theorem GlobalTheory.ArchMetric.arDeg_of_finrank_eq_one (hA : A.FG) (h1 : finrank (𝓞 K) A = 1) {x : V} (hxA : x ∈ A)
    (hx : x ≠ 0) :
    h.arDeg A = Real.log (Nat.card (A ⧸ (Submodule.span (𝓞 K) {x}).submoduleOf A)) -
      ∑ σ : K →+* ℂ, Real.log (h.norm σ x) := by sorry
