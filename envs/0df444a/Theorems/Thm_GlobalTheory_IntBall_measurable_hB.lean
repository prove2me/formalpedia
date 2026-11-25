-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_measurable_hB
-- name    : GlobalTheory.IntBall.measurable_hB
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:45:17.932055+00:00
-- url     : https://prove2.me/theorems/56dc1cdc-54cb-4970-a3d5-d90a8771790a
-- title:
--   Int Ball: measurable h B
-- statement:
--   The Int Ball construction uses the measurable h B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurableCutoffGramBoundMixedBlock.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurableCutoffGramBoundMixedBlock.lean#L8-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurableCutoffGramBoundMixedBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall

theorem GlobalTheory.IntBall.measurable_hB : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by sorry
