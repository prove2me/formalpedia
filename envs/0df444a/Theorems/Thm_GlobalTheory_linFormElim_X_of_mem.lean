-- Prove2me | Theorems.Thm_GlobalTheory_linFormElim_X_of_mem
-- name    : GlobalTheory.linFormElim_X_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:04.443649+00:00
-- url     : https://prove2.me/theorems/e0b5791c-8578-4c09-8892-910a713ab335
-- title:
--   Global Theory: lin Form Elim X of mem
-- statement:
--   The Global Theory construction uses the lin Form Elim X of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L290-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L290-L298

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

theorem GlobalTheory.linFormElim_X_of_mem {S : Set ι} {i : ι} (hi : i ∈ S) [DecidableEq J] :
    linFormElim u hu S (X (i, j₀)) = -∑ j : {j : J // j ≠ j₀},
      C ((↑hu.unit⁻¹ : R) * u j) * X ⟨(i, j.1), fun h => j.2 h.2⟩ := by sorry
