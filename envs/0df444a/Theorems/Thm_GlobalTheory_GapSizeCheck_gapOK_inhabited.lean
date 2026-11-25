-- Prove2me | Theorems.Thm_GlobalTheory_GapSizeCheck_gapOK_inhabited
-- name    : GlobalTheory.GapSizeCheck.gapOK_inhabited
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:11.447381+00:00
-- url     : https://prove2.me/theorems/28f4d796-973c-4130-8618-65ca83f6595d
-- title:
--   Gap Size Check: gap OK inhabited
-- statement:
--   The Gap Size Check construction uses the gap OK inhabited property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/KFinDecayOfDecInf.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/KFinDecayOfDecInf.lean#L8-L27

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

theorem GlobalTheory.GapSizeCheck.gapOK_inhabited (k r : ℕ) (hk : 1 ≤ k) : ∃ h : ℝ, GapOK k r h := by sorry
