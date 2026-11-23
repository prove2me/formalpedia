-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_restrict
-- name    : GlobalTheory.RandomTops.ex_restrict
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:41.069245+00:00
-- url     : https://prove2.me/theorems/11845fad-b763-484e-94f6-54eeca1e622e
-- title:
--   Random Tops: ex restrict
-- statement:
--   The Random Tops construction uses the ex restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L139-L143

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

theorem GlobalTheory.RandomTops.ex_restrict {A S : Finset ℕ} (hA : A ⊆ S) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A)) = ex δ A f := by sorry
