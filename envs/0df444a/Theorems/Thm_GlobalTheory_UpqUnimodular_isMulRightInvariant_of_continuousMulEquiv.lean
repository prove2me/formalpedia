-- Prove2me | Theorems.Thm_GlobalTheory_UpqUnimodular_isMulRightInvariant_of_continuousMulEquiv
-- name    : GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:50:28.559684+00:00
-- url     : https://prove2.me/theorems/f9271abc-8ca3-4c2a-bf55-b6060043f877
-- title:
--   Upq Unimodular: is Mul Right Invariant of continuous Mul Equiv
-- statement:
--   The Upq Unimodular construction uses the is Mul Right Invariant of continuous Mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HaarUpqIsMulRightInvariant.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HaarUpqIsMulRightInvariant.lean#L11-L28

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

theorem GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (h : (μ.map e).IsMulRightInvariant) :
    μ.IsMulRightInvariant := by sorry
