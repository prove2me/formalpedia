-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_contains
-- name    : GlobalTheory.RandomTops.ex_contains
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:59.291427+00:00
-- url     : https://prove2.me/theorems/d477e06b-bddc-421f-8b6b-032072ac95bd
-- title:
--   Random Tops: ex contains
-- statement:
--   The Random Tops construction uses the ex contains property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L199-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L199-L214

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

theorem GlobalTheory.RandomTops.ex_contains {Q B : Finset ℕ} (hQ : Q ⊆ B) :
    ex δ B (fun T => ind (Q ⊆ T)) = δ ^ Q.card := by sorry
