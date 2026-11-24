-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_span_ringOfIntegers_basis_integralPart
-- name    : GlobalTheory.MvPoly.span_ringOfIntegers_basis_integralPart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:30:37.506371+00:00
-- url     : https://prove2.me/theorems/7dbe9de9-5f60-4974-bc73-513d44d1374a
-- title:
--   Mv Poly: span ring Of Integers basis integral Part
-- statement:
--   The Mv Poly construction uses the span ring Of Integers basis integral Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L104-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L104-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsReducedBasisIntegralPartOfLinearIndependen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MvPolynomial NumberField
open GlobalTheory
open GlobalTheory.MvPoly
variable {K σ : Type*} [Field K]

theorem GlobalTheory.MvPoly.span_ringOfIntegers_basis_integralPart {W : Submodule K (MvPolynomial σ K)} {ι : Type*}
    (b : Basis ι ℤ (integralPart W)) :
    (span (𝓞 K) (Set.range fun i => (b i : MvPolynomial σ K))).restrictScalars ℤ =
      integralPart W := by sorry
