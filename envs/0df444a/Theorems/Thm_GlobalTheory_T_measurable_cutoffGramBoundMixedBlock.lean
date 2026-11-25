-- Prove2me | Theorems.Thm_GlobalTheory_T_measurable_cutoffGramBoundMixedBlock
-- name    : GlobalTheory.T.measurable_cutoffGramBoundMixedBlock
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:38.87804+00:00
-- url     : https://prove2.me/theorems/aed6b45b-83d4-5c1f-b43d-fc76456a411f
-- title:
--   T: measurable cutoff Gram Bound Mixed Block
-- statement:
--   The T construction uses the measurable cutoff Gram Bound Mixed Block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurableCutoffGramBoundMixedBlockStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurableCutoffGramBoundMixedBlockStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurableCutoffGramBoundMixedBlock
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurableCutoffGramBoundMixedBlockStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.measurable_cutoffGramBoundMixedBlock : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by sorry
