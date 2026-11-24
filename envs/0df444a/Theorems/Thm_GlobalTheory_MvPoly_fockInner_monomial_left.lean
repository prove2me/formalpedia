-- Prove2me | Theorems.Thm_GlobalTheory_MvPoly_fockInner_monomial_left
-- name    : GlobalTheory.MvPoly.fockInner_monomial_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:05.200417+00:00
-- url     : https://prove2.me/theorems/894564cf-cb6e-4932-b94d-4f5d88c36002
-- title:
--   Mv Poly: fock Inner monomial left
-- statement:
--   The Mv Poly construction uses the fock Inner monomial left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L508-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SumFinsuppAntidiagProdPowDivMultiFactorial.lean#L508-L512

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

theorem GlobalTheory.MvPoly.fockInner_monomial_left (α : σ →₀ ℕ) (c : 𝕜) (Q : MvPolynomial σ 𝕜) :
    fockInner (monomial α c) Q = multiFactorial α * (c * starRingEnd 𝕜 (Q.coeff α)) := by sorry
