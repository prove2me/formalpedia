-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_multiFactorial_add_single
-- name    : GlobalTheory.MvPoly.multiFactorial_add_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:29:43.0288+00:00
-- url     : https://prove2.me/theorems/95843a43-0765-42a1-ab70-9d45baf4216c
-- title:
--   Mv Poly: multi Factorial add single
-- statement:
--   The Mv Poly construction uses the multi Factorial add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L415-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L415-L429

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

theorem GlobalTheory.MvPoly.multiFactorial_add_single (α : σ →₀ ℕ) (i : σ) :
    multiFactorial (α + Finsupp.single i 1) = (α i + 1) * multiFactorial α := by sorry
