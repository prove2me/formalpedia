-- Prove2me | Theorems.Thm_GlobalTheory_mem_of_X_mul_mem
-- name    : GlobalTheory.mem_of_X_mul_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:20.204856+00:00
-- url     : https://prove2.me/theorems/98804bba-a98a-4ec0-852d-6fd3a1c32d26
-- title:
--   Global Theory: mem of X mul mem
-- statement:
--   The Global Theory construction uses the mem of X mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L104-L109

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

theorem GlobalTheory.mem_of_X_mul_mem {S : Set σ} {x : σ} (hx : x ∉ S) (I : Ideal R) {p : MvPolynomial σ R}
    (hp : X x * p ∈ I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S)) :
    p ∈ I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S) := by sorry
