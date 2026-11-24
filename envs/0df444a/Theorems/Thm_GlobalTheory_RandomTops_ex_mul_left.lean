-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_mul_left
-- name    : GlobalTheory.RandomTops.ex_mul_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:17.961913+00:00
-- url     : https://prove2.me/theorems/60917267-8cae-489b-9ef2-5997d5903a6b
-- title:
--   Random Tops: ex mul left
-- statement:
--   The Random Tops construction uses the ex mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L73-L77

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

theorem GlobalTheory.RandomTops.ex_mul_left (S : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => c * f T) = c * ex δ S f := by sorry
