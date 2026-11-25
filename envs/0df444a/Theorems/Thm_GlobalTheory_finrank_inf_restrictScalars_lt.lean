-- Prove2me | Theorems.Thm_GlobalTheory_finrank_inf_restrictScalars_lt
-- name    : GlobalTheory.finrank_inf_restrictScalars_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:09.324873+00:00
-- url     : https://prove2.me/theorems/4479879b-aa77-5f11-8bd2-bba2dc01ef45
-- title:
--   Global Theory: finrank inf restrict Scalars lt
-- statement:
--   The Global Theory construction uses the finrank inf restrict Scalars lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L541-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsSmulMemOfMemSpanLattice.lean#L541-L552

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
variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem GlobalTheory.finrank_inf_restrictScalars_lt {A : Submodule (𝓞 K) V} (hA : A.FG) {W : Submodule K V}
    (hW : ¬ A ≤ W.restrictScalars (𝓞 K)) :
    finrank (𝓞 K) (A ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) < finrank (𝓞 K) A := by sorry
