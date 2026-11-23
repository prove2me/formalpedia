-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_split
-- name    : GlobalTheory.RandomTops.ex_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:35.503256+00:00
-- url     : https://prove2.me/theorems/bb444b52-3176-4f21-bdee-d8e36a558630
-- title:
--   Random Tops: ex split
-- statement:
--   The Random Tops construction uses the ex split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L109-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L109-L137

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

theorem GlobalTheory.RandomTops.ex_split {A S : Finset ℕ} (hA : A ⊆ S) (f g : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A) * g (T \ A)) = ex δ A f * ex δ (S \ A) g := by sorry
