-- Prove2me | Theorems.Thm_GlobalTheory_HaarScaleMatrix_secondCountable_of_localField
-- name    : GlobalTheory.HaarScaleMatrix.secondCountable_of_localField
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:16.368074+00:00
-- url     : https://prove2.me/theorems/3899c1e0-fa22-4019-8462-a668a3f244f8
-- title:
--   Haar Scale Matrix: second Countable of local Field
-- statement:
--   The Haar Scale Matrix construction uses the second Countable of local Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureAdditiveAutomorphismScale.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureAdditiveAutomorphismScale.lean#L11-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRk
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureAdditiveAutomorphismScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory
open GlobalTheory GlobalTheory.HaarScaleMatrix
open scoped Matrix
open MeasureTheory

theorem GlobalTheory.HaarScaleMatrix.secondCountable_of_localField (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by sorry
