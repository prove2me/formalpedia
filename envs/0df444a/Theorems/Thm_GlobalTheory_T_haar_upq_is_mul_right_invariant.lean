-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_upq_is_mul_right_invariant
-- name    : GlobalTheory.T.haar_upq_is_mul_right_invariant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:13.103602+00:00
-- url     : https://prove2.me/theorems/3ec3582f-cbaa-4831-8e7e-9cd986b0d3ed
-- title:
--   T: haar upq is mul right invariant
-- statement:
--   The T construction uses the haar upq is mul right invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HaarUpqIsMulRightInvariantStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HaarUpqIsMulRightInvariantStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.BasicNotions
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_upq_is_mul_right_invariant : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by sorry
