-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_5_7
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:15.728308+00:00
-- url     : https://prove2.me/theorems/08fd2876-8e90-43bf-ba2f-82d5bbddb13e
-- title:
--   Lemma 5.7 — social welfare under F^n in terms of trade probabilities
-- statement:
--   Let $n\ge4$, $R=\sqrt n$, $q_i=R^{i-n}$ $(0\le i\le n)$, $Z=\sum_{r=1}^n1/q_r$, and let $F=F^n$ put probability $1/(Zq_i)$ on $(q_{i-1},q_i)$, $i\in[n]$. Let $V\subseteq\mathbb R_{\ge0}$ be an interval containing $q_0$ and $q_n=1$, and $M=(x,p_B,p_S)$ a measurable randomized mechanism on $V$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced. Then
--
--   $$\mathrm{SW}_M(F)=\frac1Z\sum_{i=1}^n\Bigl(\frac1R+\Bigl(1-\frac1R\Bigr)x(q_{i-1},q_i)\Bigr).$$
--
--   The identity reduces the welfare of a mechanism under $F^n$ to its trade probabilities on the support; it is the first step of the proof of Theorem 5.2.
--
--   Differences from the source:
--   - encoding: the fixed integer n ≥ 4 of the proof of Theorem 5.2, chosen with 6/√n < ε → every natural number n ≥ 4; reason: the lemma does not involve ε and every n ≥ 4 meets 6/√n < ε for some ε > 0; the same instances
--   - generalization: a WBB DSIC and IR mechanism for F (value space unnamed) → every interval value space T ⊆ [0, ∞) containing q_0 and q_n = 1, and every DSIC, IR, WBB mechanism on T; reason: the support of F^n lies in [q_0, 1] ⊆ T, and the source argument only evaluates the mechanism on [q_0, 1]; T = [0, 1] is one instance, so the statement specializes to the source claim
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 5.7; §5.2; proof in Appendix A.12, printed p. 34 (PDF p. 35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_JointObjectives
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_GeometricLaw
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 5.7, §5.2 p.34: for every integer `n ≥ 4` and every interval value space
`T ⊆ ℝ≥0` containing `q_0` and `q_n = 1` (hence the whole support), and every
DSIC, IR, WBB mechanism on `T`, the social welfare under `F^n` is
`SW_M(F) = (1/Z) Σ_{i=1}^n (1/R + (1 − 1/R)·x(q_{i−1}, q_i))`. -/
theorem lemma_5_7 (n : ℕ) (hn : 4 ≤ n) (T : Set ℝ) (hT0 : T ⊆ Set.Ici 0) (hT : T.OrdConnected)
    (hq0 : geomGrid n 0 ∈ T) (hq1 : (1 : ℝ) ∈ T) (M : SecondBestBT.Mechanism)
    (hM : IsMechanism T M) (hdsic : IsDSIC T M) (hir : IsIR T M) (hwbb : IsWBB T M) :
    SW (geomLaw n) M =
      1 / geomZ n * ∑ i ∈ Finset.Icc 1 n,
        (1 / geomRatio n + (1 - 1 / geomRatio n) * M.x (geomGrid n (i - 1), geomGrid n i)) := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
