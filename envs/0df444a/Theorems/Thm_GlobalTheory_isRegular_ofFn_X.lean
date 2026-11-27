-- Prove2me | Theorems.Thm_GlobalTheory_isRegular_ofFn_X
-- name    : GlobalTheory.isRegular_ofFn_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:42.23895+00:00
-- url     : https://prove2.me/theorems/8ba2a34d-46b5-44ac-b41c-93a8e1588146
-- title:
--   Global Theory: is Regular of Fn X
-- statement:
--   The Global Theory construction uses the is Regular of Fn X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L159-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L159-L162

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

theorem GlobalTheory.isRegular_ofFn_X [Nontrivial R] {n : ℕ} {e : Fin n → σ} (he : Function.Injective e) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (List.ofFn fun k => (X (e k) : MvPolynomial σ R)) := by sorry
