-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_prod_pow_le
-- name    : GlobalTheory.MvPoly.l1Norm_prod_pow_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:29:09.978903+00:00
-- url     : https://prove2.me/theorems/ac851a80-b6df-4d20-9bcd-6f022a3bf244
-- title:
--   Mv Poly: l1 Norm prod pow le
-- statement:
--   The Mv Poly construction uses the l1 Norm prod pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L128-L132

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

theorem GlobalTheory.MvPoly.l1Norm_prod_pow_le [NormOneClass K] {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) (c : ι → ℕ) (B : ι → ℝ) (h : ∀ i ∈ s, l1Norm (f i) ≤ B i) :
    l1Norm (∏ i ∈ s, f i ^ c i) ≤ ∏ i ∈ s, B i ^ c i := by sorry
