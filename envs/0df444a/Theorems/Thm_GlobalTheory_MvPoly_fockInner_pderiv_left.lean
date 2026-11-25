-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_fockInner_pderiv_left
-- name    : GlobalTheory.MvPoly.fockInner_pderiv_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:36.918965+00:00
-- url     : https://prove2.me/theorems/e5d971f7-eb29-4685-96a8-c45416fb6faf
-- title:
--   Mv Poly: fock Inner pderiv left
-- statement:
--   The Mv Poly construction uses the fock Inner pderiv left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L530-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L530-L532

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
variable {𝕜 : Type*} [RCLike 𝕜]

theorem GlobalTheory.MvPoly.fockInner_pderiv_left (i : σ) (P Q : MvPolynomial σ 𝕜) :
    fockInner (pderiv i P) Q = fockInner P (X i * Q) := by sorry
