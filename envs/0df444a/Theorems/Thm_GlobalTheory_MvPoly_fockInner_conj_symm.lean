-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_fockInner_conj_symm
-- name    : GlobalTheory.MvPoly.fockInner_conj_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:48.772206+00:00
-- url     : https://prove2.me/theorems/6e0e48cb-adb8-4ace-8a94-1c261275c033
-- title:
--   Mv Poly: fock Inner conj symm
-- statement:
--   The Mv Poly construction uses the fock Inner conj symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L473-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L473-L476

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

theorem GlobalTheory.MvPoly.fockInner_conj_symm (P Q : MvPolynomial σ 𝕜) :
    starRingEnd 𝕜 (fockInner P Q) = fockInner Q P := by sorry
