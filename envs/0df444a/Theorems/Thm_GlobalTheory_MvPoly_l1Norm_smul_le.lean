-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_l1Norm_smul_le
-- name    : GlobalTheory.MvPoly.l1Norm_smul_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:19.841827+00:00
-- url     : https://prove2.me/theorems/6bea544b-e6e5-5599-8e94-36e97d91864d
-- title:
--   Mv Poly: l1 Norm smul le
-- statement:
--   The Mv Poly construction uses the l1 Norm smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L112-L113

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

theorem GlobalTheory.MvPoly.l1Norm_smul_le (c : K) (P : MvPolynomial σ K) : l1Norm (c • P) ≤ ‖c‖ * l1Norm P := by sorry
