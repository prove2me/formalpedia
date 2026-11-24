-- Prove2me | Theorems.Thm_GlobalTheory_SmallIntegerVanishing_exists_denominator
-- name    : GlobalTheory.SmallIntegerVanishing.exists_denominator
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:04.037399+00:00
-- url     : https://prove2.me/theorems/2fda4f5c-752a-47b6-8dd7-d9c3390815f8
-- title:
--   Small Integer Vanishing: exists denominator
-- statement:
--   The Small Integer Vanishing construction uses the exists denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsLast.lean#L29-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsLast.lean#L29-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SmallIntegerVanishing

theorem GlobalTheory.SmallIntegerVanishing.exists_denominator (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ d : RingOfIntegers E, d ≠ 0 ∧ ∀ y ∈ Λ, ∀ a, ∃ x : RingOfIntegers E,
      (x : E) = (d : E) * y a := by sorry
