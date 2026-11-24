-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_norm_conjCoeffs_sq
-- name    : GlobalTheory.MvPoly.norm_conjCoeffs_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:29:55.544984+00:00
-- url     : https://prove2.me/theorems/6f5b34ad-112b-4560-ac18-b08d91156531
-- title:
--   Mv Poly: norm conj Coeffs sq
-- statement:
--   The Mv Poly construction uses the norm conj Coeffs sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L127-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsReducedBasisIntegralPartOfLinearIndependen.lean#L127-L135

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
variable [NumberField K] [Fintype σ]

theorem GlobalTheory.MvPoly.norm_conjCoeffs_sq [DecidableEq σ] {D : ℕ} {P : MvPolynomial σ K}
    (hP : P.totalDegree ≤ D) :
    ‖conjCoeffs K σ D P‖ ^ 2 = ∑ s : K →+* ℂ, l2Norm (map s P) ^ 2 := by sorry
