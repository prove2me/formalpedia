-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_lemma_4_8
-- name    : MoneyBurningTrade.IndependentSurplus.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:49:08.002772+00:00
-- url     : https://prove2.me/theorems/9e16ee7a-38e2-41ea-a2fa-aecfa31560af
-- title:
--   Lemma 4.8 — equal expected surpluses in the construction
-- statement:
--   For any valid parameters of the independent construction in §4.2, let $F_s,F_b$ be its continuous mixture priors and let $W$ be the normalized mechanism from its symmetric grid. Then all objectives are finite and
--
--   $$\mathrm{TS}^b_W(F_s\times F_b)=\mathrm{TS}^s_W(F_s\times F_b)=\tfrac12\mathrm{TS}_W(F_s\times F_b).$$
--
--   The equality concerns these computed priors and this computed mechanism, not arbitrary independent priors. It supplies a simultaneous per-trader conclusion from the aggregate surplus guarantee.
--
--   Differences from the source:
--   - encoding: “In the construction of Theorem 4.1” → the exact grid, continuous mixture priors and normalized mechanism as functions of valid §4.2 input parameters; reason: this makes the source’s construction dependence explicit; any k≥2 is admissible for a suitable positive ε
--   - encoding: finite expected surpluses in the bounded construction → explicit finite-objectives conclusion together with the complete equality chain; reason: the expected values are finite because the valid mechanism on [0,1] has bounded nonnegative surpluses
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.8; Appendix A.5, printed p. 30 (PDF p. 31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IndependentPriors
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Objectives

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Lemma 4.8 p.30, for the same operational priors and normalized mechanism
of §4.2. It is not asserted for arbitrary independent priors. -/
theorem lemma_4_8 (A : IndependentParameters) (hA : ValidIndependentParameters A) :
    FiniteObjectives ((sellerPrior A).prod (buyerPrior A)) (independentMechanism A) ∧
    buyerTS ((sellerPrior A).prod (buyerPrior A)) (independentMechanism A) =
      sellerTS ((sellerPrior A).prod (buyerPrior A)) (independentMechanism A) ∧
    sellerTS ((sellerPrior A).prod (buyerPrior A)) (independentMechanism A) =
      (1 / 2) * TS ((sellerPrior A).prod (buyerPrior A)) (independentMechanism A) := by sorry

end MoneyBurningTrade.IndependentSurplus
