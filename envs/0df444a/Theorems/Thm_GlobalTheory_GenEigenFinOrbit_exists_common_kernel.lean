-- Prove2me | Theorems.Thm_GlobalTheory_GenEigenFinOrbit_exists_common_kernel
-- name    : GlobalTheory.GenEigenFinOrbit.exists_common_kernel
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:50.545462+00:00
-- url     : https://prove2.me/theorems/77d0fd0c-0b8c-483c-9f23-d5716f7cd0fe
-- title:
--   Gen Eigen Fin Orbit: exists common kernel
-- statement:
--   The Gen Eigen Fin Orbit construction uses the exists common kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L78-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L78-L103

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
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)
include hcomm hst hnil

theorem GlobalTheory.GenEigenFinOrbit.exists_common_kernel [FiniteDimensional ℂ N] (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ g ∈ G, g n = 0 := by sorry
