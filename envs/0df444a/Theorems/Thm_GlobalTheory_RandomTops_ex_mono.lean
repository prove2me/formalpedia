-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_mono
-- name    : GlobalTheory.RandomTops.ex_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:32.267804+00:00
-- url     : https://prove2.me/theorems/08d767f1-b474-4b09-ac35-696d0bc423f9
-- title:
--   Random Tops: ex mono
-- statement:
--   The Random Tops construction uses the ex mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L92-L96

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

theorem GlobalTheory.RandomTops.ex_mono (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {S : Finset ℕ} {f g : Finset ℕ → ℝ}
    (h : ∀ T ⊆ S, f T ≤ g T) : ex δ S f ≤ ex δ S g := by sorry
