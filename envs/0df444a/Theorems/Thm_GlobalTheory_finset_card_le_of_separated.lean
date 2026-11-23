-- Prove2me | Theorems.Thm_GlobalTheory_finset_card_le_of_separated
-- name    : GlobalTheory.finset_card_le_of_separated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:19.953659+00:00
-- url     : https://prove2.me/theorems/651d2749-152f-4bc8-89ad-e2cda1643b2a
-- title:
--   Global Theory: finset card le of separated
-- statement:
--   The Global Theory construction uses the finset card le of separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteInterClosedBallOfSeparated.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteInterClosedBallOfSeparated.lean#L9-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem GlobalTheory.finset_card_le_of_separated (s : Finset E) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (x : E)
    (hs : ∀ a ∈ s, dist a x ≤ R) (hsep : (s : Set E).Pairwise fun a b => d ≤ dist a b) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ E := by sorry
