-- Prove2me | Theorems.Thm_GlobalTheory_invariant_right_inverse_of_right_inverse
-- name    : GlobalTheory.invariant_right_inverse_of_right_inverse
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:02.408612+00:00
-- url     : https://prove2.me/theorems/23bc5d1a-b120-4ba4-8271-c667cffc81ae
-- title:
--   Global Theory: invariant right inverse of right inverse
-- statement:
--   The Global Theory construction uses the invariant right inverse of right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantRightInverseOfRightInverse.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvariantRightInverseOfRightInverse.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInvariantRightInverseField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantRightInverseOfRightInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.invariant_right_inverse_of_right_inverse :
    ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type)
      [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L)
      (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) →
      ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by sorry
