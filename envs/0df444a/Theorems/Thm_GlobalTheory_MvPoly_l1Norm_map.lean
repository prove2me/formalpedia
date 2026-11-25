-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_map
-- name    : GlobalTheory.MvPoly.l1Norm_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:26.568163+00:00
-- url     : https://prove2.me/theorems/2d7a88f2-ed69-419b-b8b4-02b605dd1245
-- title:
--   Mv Poly: l1 Norm map
-- statement:
--   The Mv Poly construction uses the l1 Norm map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L141-L144

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

theorem GlobalTheory.MvPoly.l1Norm_map {R : Type*} [CommSemiring R] (φ : R →+* K) (P : MvPolynomial σ R) :
    l1Norm (map φ P) = ∑ α ∈ P.support, ‖φ (P.coeff α)‖ := by sorry
