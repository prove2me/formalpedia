-- Prove2me | Theorems.Thm_GlobalTheory_isWeaklyRegular_C_cons_ofFn_linForm
-- name    : GlobalTheory.isWeaklyRegular_C_cons_ofFn_linForm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:42.525952+00:00
-- url     : https://prove2.me/theorems/6d679990-6c85-4203-b826-465ef7377a2a
-- title:
--   Global Theory: is Weakly Regular C cons of Fn lin Form
-- statement:
--   The Global Theory construction uses the is Weakly Regular C cons of Fn lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L452-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L452-L456

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

theorem GlobalTheory.isWeaklyRegular_C_cons_ofFn_linForm {r : R} (hr : r ∈ nonZeroDivisors R)
    {n : ℕ} {e : Fin n → ι} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial (ι × J) R) (C r :: List.ofFn fun k => linForm u (e k)) := by sorry
