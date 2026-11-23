-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_nonneg
-- name    : GlobalTheory.MvPoly.l1Norm_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:04.060799+00:00
-- url     : https://prove2.me/theorems/27be7f98-babe-4c93-a876-e384f8cbe40d
-- title:
--   Mv Poly: l1 Norm nonneg
-- statement:
--   The Mv Poly construction uses the l1 Norm nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L42-L43

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

theorem GlobalTheory.MvPoly.l1Norm_nonneg (P : MvPolynomial σ K) : 0 ≤ l1Norm P := by sorry
