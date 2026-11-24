-- Prove2me | Theorems.Thm_GlobalTheory_UpqUnimodular_isMulRightInvariant_of_isHaarMeasure
-- name    : GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:47.754165+00:00
-- url     : https://prove2.me/theorems/ddf18c1b-1665-41d2-bb9d-e7e5382510c5
-- title:
--   Upq Unimodular: is Mul Right Invariant of is Haar Measure
-- statement:
--   The Upq Unimodular construction uses the is Mul Right Invariant of is Haar Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HaarUpqIsMulRightInvariant.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HaarUpqIsMulRightInvariant.lean#L80-L89

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.BasicNotions
noncomputable section
open GlobalTheory GlobalTheory.UpqUnimodular

theorem GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure (P Q : ℕ) (μ : Measure (UpqT P Q))
    (hμ : μ.IsHaarMeasure) : μ.IsMulRightInvariant := by sorry
