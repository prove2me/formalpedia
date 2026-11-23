-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_const
-- name    : GlobalTheory.RandomTops.ex_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:17.281383+00:00
-- url     : https://prove2.me/theorems/5c8c429f-56be-43e4-80ad-b871497193b8
-- title:
--   Random Tops: ex const
-- statement:
--   The Random Tops construction uses the ex const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L62-L65

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

theorem GlobalTheory.RandomTops.ex_const (S : Finset ℕ) (c : ℝ) : ex δ S (fun _ => c) = c := by sorry
