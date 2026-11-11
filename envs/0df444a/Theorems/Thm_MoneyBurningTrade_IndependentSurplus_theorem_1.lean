-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_theorem_1
-- name    : MoneyBurningTrade.IndependentSurplus.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:30.286194+00:00
-- url     : https://prove2.me/theorems/a318a88f-e74e-4b52-a1ab-803421179689
-- title:
--   Theorem 1 — unbounded gains for both traders
-- statement:
--   For every $\varepsilon>0$, there are independent seller and buyer probability laws $F_s,F_b$ on a common report interval $[0,1]$ and a measurable randomized DSIC, IR, WBB mechanism $W$ such that every measurable randomized DSIC, IR, SBB mechanism $M$ on the whole interval satisfies all three strict inequalities:
--
--   $$\varepsilon\,\mathrm{TS}_W(F_s\times F_b)>\mathrm{TS}_M(F_s\times F_b),$$
--   $$\varepsilon\,\mathrm{TS}^b_W(F_s\times F_b)>\mathrm{TS}^b_M(F_s\times F_b),\qquad\varepsilon\,\mathrm{TS}^s_W(F_s\times F_b)>\mathrm{TS}^s_M(F_s\times F_b).$$
--
--   Here $\mathrm{TS}^b=b x-p_B$, $\mathrm{TS}^s=p_S-sx$, and total traders' surplus is their sum. Money burnt is excluded. The same two priors, mechanism and $\varepsilon$ serve both traders and every competitor. Transfer bounds and finite-objective certificates are also conclusions, so no integrability restriction is added to the competitor class. This is the entire headline theorem, including its inseparable per-trader clause.
--
--   Differences from the source:
--   - reading: existential common interval and independent priors → witness interval [0,1], Borel laws on the reals concentrated there, and their product law; reason: §3.1 lets V be any interval in the nonnegative reals and the theorem does not name it; it is read as the existence of an instance, as in its proof, which fixes Vs = Vb = [0,1] (§4.1, Lemma 4.3); a reading for every interval V fails at the one-point interval V = {0}, where every surplus is 0 (footnote 9 says the construction extends to other intervals); every measurable randomized competitor on [0,1] is retained
--   - encoding: expectations of IR and WBB mechanisms on the bounded value square → real integrals accompanied by derived transfer bounds and finite-objective conclusions; reason: equation (9) bounds both payments and surpluses; all admissible competitors remain included
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Theorem 1, including the Moreover paragraph; Remark 4.7, printed p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Model
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Objectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB
import Definitions.Def_SecondBestBT_IsSBB
import Definitions.Def_SecondBestBT_IsPriorOn

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Theorem 1 p.4, including the entire simultaneous per-trader clause.
All measurable randomized SBB mechanisms on the full report interval compete.
The common witnesses are chosen before the competitor. -/
theorem theorem_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ (μS μB : Measure ℝ) (W : SecondBestBT.Mechanism),
      SecondBestBT.IsPriorOn reportInterval μS ∧
      SecondBestBT.IsPriorOn reportInterval μB ∧
      IsMechanism reportInterval W ∧ IsDSIC reportInterval W ∧
      IsIR reportInterval W ∧ IsWBB reportInterval W ∧
      TransferBounds W ∧ FiniteObjectives (μS.prod μB) W ∧
      ∀ M : SecondBestBT.Mechanism,
        IsMechanism reportInterval M → IsDSIC reportInterval M →
        IsIR reportInterval M → SecondBestBT.IsSBB reportInterval M →
        TransferBounds M ∧ FiniteObjectives (μS.prod μB) M ∧
        TS (μS.prod μB) M < ε * TS (μS.prod μB) W ∧
        buyerTS (μS.prod μB) M < ε * buyerTS (μS.prod μB) W ∧
        sellerTS (μS.prod μB) M < ε * sellerTS (μS.prod μB) W := by sorry

end MoneyBurningTrade.IndependentSurplus
