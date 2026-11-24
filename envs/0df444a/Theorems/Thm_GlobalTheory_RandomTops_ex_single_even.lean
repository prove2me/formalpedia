-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_single_even
-- name    : GlobalTheory.RandomTops.ex_single_even
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:15.130764+00:00
-- url     : https://prove2.me/theorems/390468e4-d8f0-4559-973b-32d68b7506a6
-- title:
--   Random Tops: ex single even
-- statement:
--   The Random Tops construction uses the ex single even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L341-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L341-L373

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

theorem GlobalTheory.RandomTops.ex_single_even (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a u : ℕ) :
    ((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1) ≤
      ex δ (Finset.Ico a (a + u)) (fun V => ind (∃ x, V = {x} ∧ Even x)) := by sorry
