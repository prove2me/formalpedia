-- Prove2me | Theorems.Thm_GlobalTheory_linFormEquiv_symm_linForm
-- name    : GlobalTheory.linFormEquiv_symm_linForm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:02.019872+00:00
-- url     : https://prove2.me/theorems/e5635bdf-dc2b-408f-8861-960e5e454729
-- title:
--   Global Theory: lin Form Equiv symm lin Form
-- statement:
--   The Global Theory construction uses the lin Form Equiv symm lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L258-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L258-L260

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

theorem GlobalTheory.linFormEquiv_symm_linForm {S : Set ι} {i : ι} (hi : i ∈ S) :
    (linFormEquiv u S j₀ hu).symm (linForm u i) = X (i, j₀) := by sorry
