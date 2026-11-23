-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_prod_le
-- name    : GlobalTheory.MvPoly.l1Norm_prod_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:28.772952+00:00
-- url     : https://prove2.me/theorems/088927ee-c200-4333-a84b-54880ac9b7b0
-- title:
--   Mv Poly: l1 Norm prod le
-- statement:
--   The Mv Poly construction uses the l1 Norm prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L115-L122

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

theorem GlobalTheory.MvPoly.l1Norm_prod_le [NormOneClass K] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) :
    l1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1Norm (f i) := by sorry
