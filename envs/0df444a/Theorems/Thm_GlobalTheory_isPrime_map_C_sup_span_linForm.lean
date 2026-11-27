-- Prove2me | Theorems.Thm_GlobalTheory_isPrime_map_C_sup_span_linForm
-- name    : GlobalTheory.isPrime_map_C_sup_span_linForm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:08.546811+00:00
-- url     : https://prove2.me/theorems/d82798c5-55b1-4a4d-8159-fab2bf5f644b
-- title:
--   Global Theory: is Prime map C sup span lin Form
-- statement:
--   The Global Theory construction uses the is Prime map C sup span lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L382-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L382-L385

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
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
include hu

theorem GlobalTheory.isPrime_map_C_sup_span_linForm (S : Set ι) (I : Ideal R) [I.IsPrime] :
    (I.map (C : R →+* MvPolynomial (ι × J) R) ⊔ Ideal.span (linForm u '' S)).IsPrime := by sorry
