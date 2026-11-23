-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_tail_le_choose
-- name    : GlobalTheory.RandomTops.tail_le_choose
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:39.28552+00:00
-- url     : https://prove2.me/theorems/e5539257-a9f4-46d6-bd83-288b4da463cd
-- title:
--   Random Tops: tail le choose
-- statement:
--   The Random Tops construction uses the tail le choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L216-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L216-L233

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

theorem GlobalTheory.RandomTops.tail_le_choose (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {B : Finset ℕ} {L : ℕ} (hB : B.card ≤ L) (K : ℕ) :
    ex δ B (fun T => ind (K ≤ T.card)) ≤ (L.choose K : ℝ) * δ ^ K := by sorry
