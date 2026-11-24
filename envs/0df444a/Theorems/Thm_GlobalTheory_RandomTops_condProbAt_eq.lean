-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_condProbAt_eq
-- name    : GlobalTheory.RandomTops.condProbAt_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:16.275873+00:00
-- url     : https://prove2.me/theorems/c31f93bd-25dd-49fd-87c3-214ff8331f23
-- title:
--   Random Tops: cond Prob At eq
-- statement:
--   The Random Tops construction uses the cond Prob At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L179-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L179-L197

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

theorem GlobalTheory.RandomTops.condProbAt_eq {n i₀ : ℕ} (hi : i₀ < n) (A : Finset ℕ → Prop) :
    condProbAt n δ i₀ A = ex δ ((Finset.range n).erase i₀) (fun U => ind (A (insert i₀ U))) := by sorry
