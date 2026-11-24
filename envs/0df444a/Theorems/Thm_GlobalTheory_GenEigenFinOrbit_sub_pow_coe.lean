-- Prove2me | Theorems.Thm_GlobalTheory_GenEigenFinOrbit_sub_pow_coe
-- name    : GlobalTheory.GenEigenFinOrbit.sub_pow_coe
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:06.70842+00:00
-- url     : https://prove2.me/theorems/6754b198-ce1b-4a4a-b5f2-66e4f98f15c8
-- title:
--   Gen Eigen Fin Orbit: sub pow coe
-- statement:
--   The Gen Eigen Fin Orbit construction uses the sub pow coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L107-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.GenEigenFinOrbit.sub_pow_coe {U : Submodule ℂ V} (z : End ℂ V) (F : End ℂ U)
    (hF : ∀ u : U, (F u : V) = z u) (c : ℂ) (k : ℕ) (u : U) :
    (((F - c • 1) ^ k) u : V) = ((z - algebraMap ℂ (End ℂ V) c) ^ k) (u : V) := by sorry
