-- Prove2me | Theorems.Thm_GlobalTheory_GenEigenFinOrbit_map_lt_of_pow_eq_zero
-- name    : GlobalTheory.GenEigenFinOrbit.map_lt_of_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:03.005014+00:00
-- url     : https://prove2.me/theorems/256d9893-9c3f-4ce8-855b-3cfcbdbfce06
-- title:
--   Gen Eigen Fin Orbit: map lt of pow eq zero
-- statement:
--   The Gen Eigen Fin Orbit construction uses the map lt of pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L16-L26

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

theorem GlobalTheory.GenEigenFinOrbit.map_lt_of_pow_eq_zero {N : Submodule ℂ V} (g : End ℂ V) (K : ℕ)
    (hg : N.map g ≤ N) (hK : ∀ n ∈ N, (g ^ K) n = 0) (hN : N ≠ ⊥) : N.map g < N := by sorry
