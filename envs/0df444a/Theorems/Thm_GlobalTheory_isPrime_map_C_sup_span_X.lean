-- Prove2me | Theorems.Thm_GlobalTheory_isPrime_map_C_sup_span_X
-- name    : GlobalTheory.isPrime_map_C_sup_span_X
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:07.268795+00:00
-- url     : https://prove2.me/theorems/4c7a1c2c-6485-556e-b659-941add174cc9
-- title:
--   Global Theory: is Prime map C sup span X
-- statement:
--   The Global Theory construction uses the is Prime map C sup span X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L164-L167

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

theorem GlobalTheory.isPrime_map_C_sup_span_X (S : Set σ) (I : Ideal R) [I.IsPrime] :
    (I.map (C : R →+* MvPolynomial σ R) ⊔ Ideal.span (X '' S)).IsPrime := by sorry
