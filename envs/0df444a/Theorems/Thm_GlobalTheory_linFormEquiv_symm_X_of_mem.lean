-- Prove2me | Theorems.Thm_GlobalTheory_linFormEquiv_symm_X_of_mem
-- name    : GlobalTheory.linFormEquiv_symm_X_of_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:46.821174+00:00
-- url     : https://prove2.me/theorems/0d3a6114-9929-4089-9409-eaecb2593eca
-- title:
--   Global Theory: lin Form Equiv symm X of mem
-- statement:
--   The Global Theory construction uses the lin Form Equiv symm X of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L266-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L266-L268

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

theorem GlobalTheory.linFormEquiv_symm_X_of_mem {S : Set ι} {i : ι} (hi : i ∈ S) :
    (linFormEquiv u S j₀ hu).symm (X (i, j₀)) = linForm (linFormInvCoeff u j₀ hu) i := by sorry
