-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_card_support_le_choose
-- name    : GlobalTheory.MvPoly.card_support_le_choose
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:01.922203+00:00
-- url     : https://prove2.me/theorems/8453773e-22af-4442-9415-14c1b88c745d
-- title:
--   Mv Poly: card support le choose
-- statement:
--   The Mv Poly construction uses the card support le choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L299-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L299-L302

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
variable [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ]

theorem GlobalTheory.MvPoly.card_support_le_choose {R : Type*} [CommSemiring R] {P : MvPolynomial σ R} {d : ℕ}
    (h : P.totalDegree ≤ d) : #P.support ≤ (Fintype.card σ + d).choose d := by sorry
