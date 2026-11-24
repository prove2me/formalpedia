-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzDiv_hasTemperateGrowth_invCut
-- name    : GlobalTheory.SchwartzDiv.hasTemperateGrowth_invCut
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:24.639015+00:00
-- url     : https://prove2.me/theorems/1c84bb3e-9289-4e7d-96ca-310a56b1ac96
-- title:
--   Schwartz Div: has Temperate Growth inv Cut
-- statement:
--   The Schwartz Div construction uses the has Temperate Growth inv Cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L83-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L83-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
open GlobalTheory GlobalTheory.SchwartzDiv

theorem GlobalTheory.SchwartzDiv.hasTemperateGrowth_invCut : invCut.HasTemperateGrowth := by sorry
