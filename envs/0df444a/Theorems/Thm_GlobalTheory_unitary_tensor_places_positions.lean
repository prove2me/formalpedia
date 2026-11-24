-- Prove2me | Theorems.Thm_GlobalTheory_unitary_tensor_places_positions
-- name    : GlobalTheory.unitary_tensor_places_positions
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:19.089807+00:00
-- url     : https://prove2.me/theorems/5e849c7f-dcd9-486c-afbd-9008ef07d49c
-- title:
--   Global Theory: unitary tensor places positions
-- statement:
--   The Global Theory construction uses the unitary tensor places positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryTensorPlacesSlots.lean#L24-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryTensorPlacesSlots.lean#L24-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryTensorPlacesSlots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
open GlobalTheory

theorem GlobalTheory.unitary_tensor_places_positions : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι]
    [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) →
    (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈
      Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by sorry
