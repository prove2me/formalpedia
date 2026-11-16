-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_5_3
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:40:41.20721+00:00
-- url     : https://prove2.me/theorems/c0f46506-7f99-407b-8079-19d8c908267e
-- title:
--   Lemma 5.3 — gains from trade in terms of A(r)
-- statement:
--   Let $t\ge4$, $\lambda=1/(1-e^{-t})$, and let $F_s,F_b$ be the laws (23) on $[0,t]$ with densities $\lambda e^{z-t}$ and $\lambda e^{-z}$. Let $M=(x,p_B,p_S)$ be a measurable randomized mechanism on $[0,t]$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced, and let $A(r)=\int_0^{t-r}x(v,v+r)\,dv$ as in (25). Then
--
--   $$\mathrm{GFT}_M(F_s\times F_b)=\lambda^2e^{-t}\int_0^t r\,e^{-r}A(r)\,dr.$$
--
--   The identity reduces the gains from trade of any such mechanism to a one-dimensional integral of the trade mass at each gain $r$; it is the first step of the proof of Theorem 5.1.
--
--   **Formalization Note** $\mathrm{GFT}_M(F_s\times F_b)=\int(v_b-v_s)\,x(v_s,v_b)\,d(F_s\otimes F_b)$ is the published `SecondBestBT.gft`.
--
--   Differences from the source:
--   - encoding: the fixed t ≥ 4 of the proof of Theorem 5.1, chosen with (24) → every real t ≥ 4; reason: the lemma does not involve ε and every t ≥ 4 meets (24) for some ε > 0; the same instances
--   - reading: a WBB DSIC and IR mechanism for F_s × F_b, value space unnamed; both laws are supported on [0, t] → mechanisms measurable on, and DSIC, IR, WBB over, the value space [0, t]; reason: [0, t] is the interval the paper names as the support; a mechanism on any larger interval restricts to [0, t] with all properties intact
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 5.3; §5.1; proof in Appendix A.9, printed p. 32 (PDF p. 33); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_ExponentialLaws
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB
import Definitions.Def_SecondBestBT_gft

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 5.3, §5.1 p.32: for every `t ≥ 4` and every DSIC, IR, WBB mechanism `M` on
`[0, t]`, the gains-from-trade under the laws (23) are
`GFT_M(F_s × F_b) = λ² e^(−t) ∫_0^t r e^(−r) A(r) dr`, with `A` from (25). -/
theorem lemma_5_3 (t : ℝ) (ht : 4 ≤ t) (M : SecondBestBT.Mechanism)
    (hM : IsMechanism (Set.Icc 0 t) M) (hdsic : IsDSIC (Set.Icc 0 t) M)
    (hir : IsIR (Set.Icc 0 t) M) (hwbb : IsWBB (Set.Icc 0 t) M) :
    SecondBestBT.gft (bdSellerLaw t) (bdBuyerLaw t) M.x =
      bdLambda t ^ 2 * Real.exp (-t) *
        ∫ r in (0 : ℝ)..t, r * Real.exp (-r) * tradeMass M t r := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
