-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_pow_le
-- name    : GlobalTheory.MvPoly.l1Norm_pow_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:29:22.107974+00:00
-- url     : https://prove2.me/theorems/e199762b-8de3-418c-86fc-9cbadc20ee2c
-- title:
--   Mv Poly: l1 Norm pow le
-- statement:
--   The Mv Poly construction uses the l1 Norm pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L124-L126

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

theorem GlobalTheory.MvPoly.l1Norm_pow_le [NormOneClass K] (P : MvPolynomial σ K) (n : ℕ) :
    l1Norm (P ^ n) ≤ l1Norm P ^ n := by sorry
