-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_one_sub
-- name    : GlobalTheory.RandomTops.ex_one_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:28.707805+00:00
-- url     : https://prove2.me/theorems/e104e9ca-5a68-4bd0-b1cc-f1e5dfbe353a
-- title:
--   Random Tops: ex one sub
-- statement:
--   The Random Tops construction uses the ex one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L79-L84

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

theorem GlobalTheory.RandomTops.ex_one_sub (S : Finset ℕ) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => 1 - f T) = 1 - ex δ S f := by sorry
