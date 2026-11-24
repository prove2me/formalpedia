-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_fockInner_X_mul_left
-- name    : GlobalTheory.MvPoly.fockInner_X_mul_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:38.15961+00:00
-- url     : https://prove2.me/theorems/57372b11-c1ca-41e2-9d68-948ebac7d948
-- title:
--   Mv Poly: fock Inner X mul left
-- statement:
--   The Mv Poly construction uses the fock Inner X mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L520-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L520-L528

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

theorem GlobalTheory.MvPoly.fockInner_X_mul_left (i : σ) (P Q : MvPolynomial σ 𝕜) :
    fockInner (X i * P) Q = fockInner P (pderiv i Q) := by sorry
