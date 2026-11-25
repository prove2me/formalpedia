-- Prove2me | Theorems.Thm_GlobalTheory_GapSizeCheck_thresholds
-- name    : GlobalTheory.GapSizeCheck.thresholds
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:06.528399+00:00
-- url     : https://prove2.me/theorems/7ad1f064-392d-4bfe-a16f-8cf68cd3c450
-- title:
--   Gap Size Check: thresholds
-- statement:
--   The Gap Size Check construction uses the thresholds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/KFinDecayOfDecInf.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/KFinDecayOfDecInf.lean#L29-L41

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.ThreeDimData
open GlobalTheory GlobalTheory.GapSizeCheck

theorem GlobalTheory.GapSizeCheck.thresholds (k r : ℕ) (h : ℝ) (hg : GapOK k r h) :
    AG k r < (aOf r h - 1) / 2 ∧ AS k r < (aOf r h - 1) / 2 ∧
      (2 * Mexp r * AS k r + 1) + AG k r + 1 ≤ aOf r h - 1 := by sorry
