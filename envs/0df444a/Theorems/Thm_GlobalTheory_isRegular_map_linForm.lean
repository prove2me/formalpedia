-- Prove2me | Theorems.Thm_GlobalTheory_isRegular_map_linForm
-- name    : GlobalTheory.isRegular_map_linForm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:31.458005+00:00
-- url     : https://prove2.me/theorems/0264f23b-7b41-4d68-b4bd-2e96736a2ea7
-- title:
--   Global Theory: is Regular map lin Form
-- statement:
--   The Global Theory construction uses the is Regular map lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L425-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L425-L427

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

theorem GlobalTheory.isRegular_map_linForm [Nontrivial R] {l : List ι} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial (ι × J) R) (l.map (linForm u)) := by sorry
