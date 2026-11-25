-- Prove2me | Theorems.Thm_GlobalTheory_SmallIntegerVanishing_main
-- name    : GlobalTheory.SmallIntegerVanishing.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:01.235416+00:00
-- url     : https://prove2.me/theorems/9eae9cda-8b23-46bc-beea-10c00224ca77
-- title:
--   Small Integer Vanishing: main
-- statement:
--   The Small Integer Vanishing construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsLast.lean#L67-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsLast.lean#L67-L90

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

theorem GlobalTheory.SmallIntegerVanishing.main (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ,
      (∀ (w : InfinitePlace E) (a : Fin j), w (y a) < δ) → y = 0 := by sorry
