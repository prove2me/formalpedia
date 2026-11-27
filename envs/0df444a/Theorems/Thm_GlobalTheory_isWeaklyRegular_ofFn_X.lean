-- Prove2me | Theorems.Thm_GlobalTheory_isWeaklyRegular_ofFn_X
-- name    : GlobalTheory.isWeaklyRegular_ofFn_X
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:21.26307+00:00
-- url     : https://prove2.me/theorems/adac2fa6-6a6d-49d1-ac46-8ca4155230a7
-- title:
--   Global Theory: is Weakly Regular of Fn X
-- statement:
--   The Global Theory construction uses the is Weakly Regular of Fn X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L154-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L154-L157

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

theorem GlobalTheory.isWeaklyRegular_ofFn_X {n : ℕ} {e : Fin n → σ} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial σ R) (List.ofFn fun k => (X (e k) : MvPolynomial σ R)) := by sorry
