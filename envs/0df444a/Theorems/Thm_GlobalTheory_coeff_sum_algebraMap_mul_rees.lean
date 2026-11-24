-- Prove2me | Theorems.Thm_GlobalTheory_coeff_sum_algebraMap_mul_rees
-- name    : GlobalTheory.coeff_sum_algebraMap_mul_rees
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:51.651544+00:00
-- url     : https://prove2.me/theorems/558f52df-b076-46b1-a706-68c3058a6e8c
-- title:
--   Global Theory: coeff sum algebra Map mul rees
-- statement:
--   The Global Theory construction uses the coeff sum algebra Map mul rees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGradedRingKernelLift.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGradedRingKernelLift.lean#L24-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.coeff_sum_algebraMap_mul_rees {R : Type} [CommRing R] {I : Ideal R} {a : ℕ}
    (r : Fin a → R) (p : Fin a → reesAlgebra I) (n : ℕ) :
    ((∑ k, algebraMap R (reesAlgebra I) (r k) * p k : reesAlgebra I) : R[X]).coeff n
      = ∑ k, r k * (p k : R[X]).coeff n := by sorry
