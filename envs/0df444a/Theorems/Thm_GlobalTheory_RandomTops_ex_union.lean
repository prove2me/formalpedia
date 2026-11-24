-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_union
-- name    : GlobalTheory.RandomTops.ex_union
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:19.556333+00:00
-- url     : https://prove2.me/theorems/666591ed-7e11-49c0-974d-cae821c996e8
-- title:
--   Random Tops: ex union
-- statement:
--   The Random Tops construction uses the ex union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L98-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L98-L107

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}

theorem GlobalTheory.RandomTops.ex_union {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    ex δ (A ∪ B) f = ex δ A (fun T => ex δ B (fun U => f (T ∪ U))) := by sorry
