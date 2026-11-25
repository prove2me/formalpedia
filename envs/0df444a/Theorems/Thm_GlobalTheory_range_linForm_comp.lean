-- Prove2me | Theorems.Thm_GlobalTheory_range_linForm_comp
-- name    : GlobalTheory.range_linForm_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:44.485797+00:00
-- url     : https://prove2.me/theorems/05a9e1c4-8a21-57f9-aab3-69c2c199a3e7
-- title:
--   Global Theory: range lin Form comp
-- statement:
--   The Global Theory construction uses the range lin Form comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L376-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L376-L378

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

theorem GlobalTheory.range_linForm_comp {κ : Type*} (e : κ → ι) :
    Set.range (fun k => linForm u (e k)) = linForm u '' Set.range e := by sorry
