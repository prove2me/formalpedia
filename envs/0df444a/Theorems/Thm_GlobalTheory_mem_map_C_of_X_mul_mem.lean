-- Prove2me | Theorems.Thm_GlobalTheory_mem_map_C_of_X_mul_mem
-- name    : GlobalTheory.mem_map_C_of_X_mul_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:21.804008+00:00
-- url     : https://prove2.me/theorems/82cefa53-1c2c-4d9d-9237-70880861b673
-- title:
--   Global Theory: mem map C of X mul mem
-- statement:
--   The Global Theory construction uses the mem map C of X mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L96-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {σ : Type*}

theorem GlobalTheory.mem_map_C_of_X_mul_mem (x : σ) (I : Ideal R) {p : MvPolynomial σ R}
    (hp : X x * p ∈ I.map (C : R →+* MvPolynomial σ R)) :
    p ∈ I.map (C : R →+* MvPolynomial σ R) := by sorry
