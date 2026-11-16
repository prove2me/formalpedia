-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_5_4
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:14.755579+00:00
-- url     : https://prove2.me/theorems/f0eceded-f837-472c-b1d3-bad584856b25
-- title:
--   Lemma 5.4 — little trade at profiles with a small gain from trade
-- statement:
--   Let $t\ge4$ and let $M=(x,p_B,p_S)$ be a measurable randomized mechanism on $[0,t]$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced, with $A(r)=\int_0^{t-r}x(v,v+r)\,dv$ as in (25). Then
--
--   $$\int_0^t r\,e^{-r}A(r)\,dr\le1+\frac{11}{e}\Bigl(\frac12+\log t\Bigr),\tag{26}$$
--
--   with the natural logarithm. Combined with Lemma 5.3 it bounds the gains from trade of every such mechanism under the laws (23) by $\lambda^2e^{-t}(1+\frac{11}{e}(\frac12+\log t))$.
--
--   Differences from the source:
--   - encoding: the fixed t ≥ 4 of the proof of Theorem 5.1, chosen with (24) → every real t ≥ 4; reason: the lemma does not involve ε and every t ≥ 4 meets (24) for some ε > 0; the same instances
--   - reading: a WBB DSIC and IR mechanism for F_s × F_b, value space unnamed; both laws are supported on [0, t] → mechanisms measurable on, and DSIC, IR, WBB over, the value space [0, t]; reason: [0, t] is the interval the paper names as the support; a mechanism on any larger interval restricts to [0, t] with all properties intact
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 5.4, inequality (26); §5.1; proof in Appendix A.10, printed p. 33 (PDF p. 34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_ExponentialLaws
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 5.4, §5.1 p.33, inequality (26): for every `t ≥ 4` and every DSIC, IR, WBB
mechanism on `[0, t]`, `∫_0^t r e^(−r) A(r) dr ≤ 1 + (11/e)(1/2 + log t)`
(natural logarithm). -/
theorem lemma_5_4 (t : ℝ) (ht : 4 ≤ t) (M : SecondBestBT.Mechanism)
    (hM : IsMechanism (Set.Icc 0 t) M) (hdsic : IsDSIC (Set.Icc 0 t) M)
    (hir : IsIR (Set.Icc 0 t) M) (hwbb : IsWBB (Set.Icc 0 t) M) :
    ∫ r in (0 : ℝ)..t, r * Real.exp (-r) * tradeMass M t r ≤
      1 + 11 / Real.exp 1 * (1 / 2 + Real.log t) := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
