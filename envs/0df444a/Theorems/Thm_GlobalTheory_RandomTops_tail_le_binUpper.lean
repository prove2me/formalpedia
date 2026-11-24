-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_tail_le_binUpper
-- name    : GlobalTheory.RandomTops.tail_le_binUpper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:37.005483+00:00
-- url     : https://prove2.me/theorems/33c2883b-cb00-4e6f-9818-f620c2c04340
-- title:
--   Random Tops: tail le bin Upper
-- statement:
--   The Random Tops construction uses the tail le bin Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L252-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L252-L259

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

theorem GlobalTheory.RandomTops.tail_le_binUpper (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A : Finset ℕ} {G : ℕ} (hA : A.card ≤ G)
    (K : ℕ) : ex δ A (fun T => ind (K ≤ T.card)) ≤ binUpper G δ K := by sorry
