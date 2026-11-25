-- Prove2me | Theorems.Thm_GlobalTheory_Phase_pair_int
-- name    : GlobalTheory.Phase.pair_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:42.226019+00:00
-- url     : https://prove2.me/theorems/0d903c23-ac4d-4f69-b267-b1779f336f2c
-- title:
--   Phase: pair int
-- statement:
--   The Phase construction uses the pair int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L95-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
open GlobalTheory GlobalTheory.Phase
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable {n g : ℕ}

theorem GlobalTheory.Phase.pair_int {a b : Matrix κ ι ℚ} (ha : ∀ k i, ∃ z : ℤ, a k i = z) (hb : ∀ k i, ∃ z : ℤ, b k i = z) :
    ∃ z : ℤ, (∑ k, a k ⬝ᵥ b k : ℚ) = z := by sorry
