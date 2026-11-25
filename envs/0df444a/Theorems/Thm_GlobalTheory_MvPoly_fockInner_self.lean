-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_fockInner_self
-- name    : GlobalTheory.MvPoly.fockInner_self
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:14.672196+00:00
-- url     : https://prove2.me/theorems/4ef3b1b7-e43e-5f12-8132-9e9defc957fc
-- title:
--   Mv Poly: fock Inner self
-- statement:
--   The Mv Poly construction uses the fock Inner self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L505-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L505-L506

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

theorem GlobalTheory.MvPoly.fockInner_self (P : MvPolynomial σ 𝕜) : fockInner P P = (fockNormSq P : 𝕜) := by sorry
