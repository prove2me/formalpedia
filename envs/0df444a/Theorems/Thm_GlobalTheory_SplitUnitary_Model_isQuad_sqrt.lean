-- Prove2me | Theorems.Thm_GlobalTheory_SplitUnitary_Model_isQuad_sqrt
-- name    : GlobalTheory.SplitUnitary.Model.isQuad_sqrt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:13:03.80406+00:00
-- url     : https://prove2.me/theorems/0401fffe-1392-4bf8-93cb-0ae56a2ec531
-- title:
--   Model: is Quad sqrt
-- statement:
--   The Model construction uses the is Quad sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L16-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_SumSquaresNeThreeThreeAdic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ConclRankZeroRight
import Theorems.Thm_GlobalTheory_HermLocal_Model_conjSqrt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.SplitUnitary GlobalTheory.SplitUnitary.Model
open GlobalTheory.WeilM (UG hTens IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB IsSmoothRep nabs)
open GlobalTheory.HermLocal.Model (conjSqrt conjSqrt_apply)

theorem GlobalTheory.SplitUnitary.Model.isQuad_sqrt {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] :
    IsQuad (conjSqrt d : QuadraticAlgebra K d 0 →ₐ[K] QuadraticAlgebra K d 0) QuadraticAlgebra.omega := by sorry
