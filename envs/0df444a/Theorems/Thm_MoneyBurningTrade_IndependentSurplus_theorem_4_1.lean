-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_theorem_4_1
-- name    : MoneyBurningTrade.IndependentSurplus.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:49:27.05546+00:00
-- url     : https://prove2.me/theorems/72026c0e-5662-4560-9f4f-46bc0063f0c6
-- title:
--   Theorem 4.1 — aggregate surplus separation
-- statement:
--   For every $\varepsilon>0$, the construction of §4.2 supplies $k\ge2$ with $(k-1)/12\ge1/\varepsilon$, valid parameters $\tau,\eta,R$, independent continuous mixture priors $F_s,F_b$ on $[0,1]$ and their normalized measurable randomized DSIC, IR, WBB mechanism $W$. Every measurable randomized DSIC, IR, SBB competitor $M$ on the full report interval satisfies
--
--   $$\varepsilon\,\mathrm{TS}_W(F_s\times F_b)>\mathrm{TS}_M(F_s\times F_b)=\mathrm{GFT}_M(F_s\times F_b).$$
--
--   Probability normalization and support of the constructed laws, transfer bounds, and finiteness of every objective of both mechanisms are conclusions. The same constructed laws and mechanism precede the universal competitor. This is the aggregate separation used for the complete goal's per-trader guarantees.
--
--   Differences from the source:
--   - reading: existential common interval and independent priors → witness interval [0,1], Borel laws on the reals concentrated there, and their product law; reason: §3.1 lets V be any interval in the nonnegative reals and the theorem does not name it; it is read as the existence of an instance, as in its proof, which fixes Vs = Vb = [0,1] (§4.1, Lemma 4.3); a reading for every interval V fails at the one-point interval V = {0}, where every surplus is 0 (footnote 9 says the construction extends to other intervals); every measurable randomized competitor on [0,1] is retained
--   - encoding: expectations of IR and WBB mechanisms on the bounded value square → real integrals accompanied by derived transfer bounds and finite-objective conclusions; reason: equation (9) bounds both payments and surpluses; all admissible competitors remain included
--   - generalization: the existential priors and WBB mechanism of Theorem 4.1 → the operational continuous mixtures and normalized mechanism of its §4.2 proof, with (k−1)/12≥1/ε; reason: the Lean names the §4.2 witnesses, which implies the source’s bare existential; normalization and support are conclusions, and nothing is imposed on any competitor
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Theorem 4.1; §4.2, printed p. 18; construction 26–28 (PDF p. 19; construction 27–29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IndependentPriors
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Objectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB
import Definitions.Def_SecondBestBT_IsSBB
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_gft

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Theorem 4.1 p.18, with the witnesses constructed in §4.2 pp.26–28.
The extra normalization, boundedness and integrability conclusions certify the
meaning of all expectations; no competitor is excluded for integrability. -/
theorem theorem_4_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ A : IndependentParameters,
      ValidIndependentParameters A ∧
      1 / ε ≤ ((A.k : ℝ) - 1) / 12 ∧
      SecondBestBT.IsPriorOn reportInterval (sellerPrior A) ∧
      SecondBestBT.IsPriorOn reportInterval (buyerPrior A) ∧
      IsMechanism reportInterval (independentMechanism A) ∧
      IsDSIC reportInterval (independentMechanism A) ∧
      IsIR reportInterval (independentMechanism A) ∧
      IsWBB reportInterval (independentMechanism A) ∧
      TransferBounds (independentMechanism A) ∧
      FiniteObjectives ((sellerPrior A).prod (buyerPrior A)) (independentMechanism A) ∧
      ∀ M : SecondBestBT.Mechanism,
        IsMechanism reportInterval M → IsDSIC reportInterval M →
        IsIR reportInterval M → SecondBestBT.IsSBB reportInterval M →
        TransferBounds M ∧ FiniteObjectives ((sellerPrior A).prod (buyerPrior A)) M ∧
        TS ((sellerPrior A).prod (buyerPrior A)) M <
          ε * TS ((sellerPrior A).prod (buyerPrior A)) (independentMechanism A) ∧
        TS ((sellerPrior A).prod (buyerPrior A)) M =
          SecondBestBT.gft (sellerPrior A) (buyerPrior A) M.x := by sorry

end MoneyBurningTrade.IndependentSurplus
