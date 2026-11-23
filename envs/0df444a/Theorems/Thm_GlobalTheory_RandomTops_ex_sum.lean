-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_sum
-- name    : GlobalTheory.RandomTops.ex_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:43.472802+00:00
-- url     : https://prove2.me/theorems/bab5576d-a2e8-4db6-b053-3114217867de
-- title:
--   Random Tops: ex sum
-- statement:
--   The Random Tops construction uses the ex sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L86-L90

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

theorem GlobalTheory.RandomTops.ex_sum {ι : Type*} (S : Finset ℕ) (I : Finset ι) (f : ι → Finset ℕ → ℝ) :
    ex δ S (fun T => ∑ i ∈ I, f i T) = ∑ i ∈ I, ex δ S (f i) := by sorry
