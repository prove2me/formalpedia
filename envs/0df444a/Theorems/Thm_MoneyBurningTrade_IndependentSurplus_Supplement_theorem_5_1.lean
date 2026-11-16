-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_theorem_5_1
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:34.174876+00:00
-- url     : https://prove2.me/theorems/a28679c2-699f-4486-ab4a-d8023c23f676
-- title:
--   Theorem 5.1 — independent values: WBB cannot approximate first-best gains from trade
-- statement:
--   For every $\varepsilon>0$ there are $t>0$ and independent seller and buyer laws $F_s,F_b$, probability measures supported on $[0,t]$, such that every measurable randomized mechanism $M$ on the value space $[0,t]$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced (strongly budget-balanced ones included) satisfies
--
--   $$\mathrm{TS}_M(F_s\times F_b)\le\mathrm{GFT}_M(F_s\times F_b)<\varepsilon\cdot\mathrm{GFT}_{\mathrm{OPT}}(F_s\times F_b)=\varepsilon\cdot\mathrm{TS}_{\mathrm{OPT}}(F_s\times F_b),$$
--
--   and all objectives of $M$ are finite. Here $\mathrm{TS}$ is the traders' surplus (burnt money excluded), $\mathrm{GFT}$ the gains from trade (burnt money included) and $\mathrm{GFT}_{\mathrm{OPT}}=\mathbb E[\max\{v_b-v_s,0\}]$; the first best burns no money, so $\mathrm{TS}_{\mathrm{OPT}}=\mathrm{GFT}_{\mathrm{OPT}}$ by definition. The laws are chosen before the mechanism.
--
--   Thus money burning, although it can beat every strongly budget-balanced mechanism (Theorem 4.1), still cannot guarantee any constant fraction of the first-best gains from trade.
--
--   Differences from the source:
--   - reading: existential independent distributions F_s, F_b with the value space unnamed → an existential t > 0, laws concentrated on [0, t], their product law, and competitors on the value space [0, t]; reason: the proof fixes laws supported on [0, t] (23); [0, t] is that support, and a mechanism on any larger interval restricts to [0, t] with all properties intact
--   - encoding: expectations of the objectives → Bochner integrals together with finite-objective (integrability) conclusions for every admissible mechanism; reason: (9) bounds payments and surpluses on a bounded value square, so all are finite; stating it as a conclusion excludes no competitor and rules out the default value 0 of a non-integrable integral
--   - encoding: the closing equality ε·GFT_OPT = ε·TS_OPT → stated through GFT_OPT only; reason: §3.3 (printed p. 17) defines TS_OPT(F) = GFT_OPT(F); the equality is definitional
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Theorem 5.1 (= Theorem 3, statement 1, of the introduction, printed p. 6); proof in §5.1, printed pp. 32–33, printed p. 32 (PDF p. 33); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_JointObjectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB
import Definitions.Def_SecondBestBT_IsPriorOn
import Definitions.Def_SecondBestBT_gft
import Definitions.Def_SecondBestBT_firstBest

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Theorem 5.1, §5 p.32: for every `ε > 0` there are `t > 0` and independent seller and
buyer laws on `[0, t]` such that every DSIC, IR, WBB mechanism `M` on `[0, t]` (SBB
ones included) has `TS_M ≤ GFT_M < ε·GFT_OPT` under `F_s × F_b`. By the paper's
definition `TS_OPT = GFT_OPT`. The laws precede the competitor; integrability of
every objective is a conclusion. -/
theorem theorem_5_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ (t : ℝ) (μS μB : Measure ℝ), 0 < t ∧
      SecondBestBT.IsPriorOn (Set.Icc 0 t) μS ∧
      SecondBestBT.IsPriorOn (Set.Icc 0 t) μB ∧
      ∀ M : SecondBestBT.Mechanism,
        IsMechanism (Set.Icc 0 t) M → IsDSIC (Set.Icc 0 t) M →
        IsIR (Set.Icc 0 t) M → IsWBB (Set.Icc 0 t) M →
        FiniteJointObjectives (μS.prod μB) M ∧
        TS (μS.prod μB) M ≤ SecondBestBT.gft μS μB M.x ∧
        SecondBestBT.gft μS μB M.x < ε * SecondBestBT.firstBest μS μB := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
