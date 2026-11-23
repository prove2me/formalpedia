-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_insert
-- name    : GlobalTheory.RandomTops.ex_insert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:18.148561+00:00
-- url     : https://prove2.me/theorems/3cd605f6-97d0-4198-9420-36d19da3c5de
-- title:
--   Random Tops: ex insert
-- statement:
--   The Random Tops construction uses the ex insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L43-L55

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

theorem GlobalTheory.RandomTops.ex_insert {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : Finset ℕ → ℝ) :
    ex δ (insert a S) f = (1 - δ) * ex δ S f + δ * ex δ S (fun T => f (insert a T)) := by sorry
