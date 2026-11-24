-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_add
-- name    : GlobalTheory.RandomTops.ex_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:17.451525+00:00
-- url     : https://prove2.me/theorems/56a6ae9c-460a-44e4-86bf-e0b3e8d1f291
-- title:
--   Random Tops: ex add
-- statement:
--   The Random Tops construction uses the ex add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L67-L71

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

theorem GlobalTheory.RandomTops.ex_add (S : Finset ℕ) (f g : Finset ℕ → ℝ) :
    ex δ S (fun T => f T + g T) = ex δ S f + ex δ S g := by sorry
