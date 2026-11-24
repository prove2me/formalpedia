-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_vectorL2Norm_const_mul
-- name    : GlobalTheory.MvPoly.vectorL2Norm_const_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:30:20.444927+00:00
-- url     : https://prove2.me/theorems/f901b2ba-9c0f-42c9-aaea-821daa4742b9
-- title:
--   Mv Poly: vector L2 Norm const mul
-- statement:
--   The Mv Poly construction uses the vector L2 Norm const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L346-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L346-L350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K] [NormedCommRing L]

theorem GlobalTheory.MvPoly.vectorL2Norm_const_mul [NormMulClass K] (c : K) (P : MvPolynomial σ K) :
    l2Norm (c • P) = ‖c‖ * l2Norm P := by sorry
