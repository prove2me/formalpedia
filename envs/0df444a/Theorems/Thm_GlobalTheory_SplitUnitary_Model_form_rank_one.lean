-- Prove2me | Theorems.Thm_GlobalTheory_SplitUnitary_Model_form_rank_one
-- name    : GlobalTheory.SplitUnitary.Model.form_rank_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:26.58293+00:00
-- url     : https://prove2.me/theorems/e9c9fcf8-7059-4d53-a917-96b2c2c2b826
-- title:
--   Model: form rank one
-- statement:
--   The Model construction uses the form rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/ConclRankZeroRight.lean#L61-L64

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
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)

theorem GlobalTheory.SplitUnitary.Model.form_rank_one (q x y : E) :
    form (α := Unit) (ν := Unit) c (fun _ _ => q) (fromCols (fun _ _ => x) 0) (fromCols 0 (fun _ _ => y)) =
      2⁻¹ * Algebra.trace F E (x * q * c y) := by sorry
