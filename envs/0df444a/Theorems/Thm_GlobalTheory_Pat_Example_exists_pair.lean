-- Prove2me | Theorems.Thm_GlobalTheory_Pat_Example_exists_pair
-- name    : GlobalTheory.Pat.Example.exists_pair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:51.620021+00:00
-- url     : https://prove2.me/theorems/5b646993-2e8b-5f3c-818a-2f21e4f2b86b
-- title:
--   Example: exists pair
-- statement:
--   The Example construction uses the exists pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L793-L795
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L793-L795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
noncomputable section
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.Pat GlobalTheory.Pat.Example

theorem GlobalTheory.Pat.Example.exists_pair : ∃ (Φ : Frame) (G : PolGp Φ), Φ.n = 2 ∧ Nonempty Φ.Vl ∧ Nonempty Φ.St ∧
    Nat.card G.Γ = 6 ∧ Nonempty (Pair G) := by sorry
