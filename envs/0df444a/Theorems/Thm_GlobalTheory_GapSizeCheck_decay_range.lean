-- Prove2me | Theorems.Thm_GlobalTheory_GapSizeCheck_decay_range
-- name    : GlobalTheory.GapSizeCheck.decay_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:24.385116+00:00
-- url     : https://prove2.me/theorems/d2b666e5-80af-4647-aedb-23815f6dae41
-- title:
--   Gap Size Check: decay range
-- statement:
--   The Gap Size Check construction uses the decay range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/KFinDecayOfDecInf.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/KFinDecayOfDecInf.lean#L43-L53

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

theorem GlobalTheory.GapSizeCheck.decay_range (k r : ℕ) (h : ℝ) (h120 : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) * (((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1)) ≤ h := by sorry
