-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_5_8
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:43:46.717514+00:00
-- url     : https://prove2.me/theorems/4bc6a71b-a6de-41e6-bd33-aeac151a4c50
-- title:
--   Lemma 5.8 — allocation bound on the geometric grid
-- statement:
--   Let $n\ge4$, $R=\sqrt n$ and $q_i=R^{i-n}$ $(0\le i\le n)$. Let $V\subseteq\mathbb R_{\ge0}$ be an interval containing $q_0$ and $q_n=1$, and $M=(x,p_B,p_S)$ a measurable randomized mechanism on $V$ that is dominant-strategy incentive compatible, individually rational and weakly budget balanced. Then
--
--   $$\sum_{i=1}^n x(q_{i-1},q_i)\le5R.\tag{29}$$
--
--   The sum starts at $i=1$. Since $F^n$ gives each profile $(q_{i-1},q_i)$ weight inversely proportional to $q_i$, this caps the welfare of every such mechanism in the proof of Theorem 5.2.
--
--   Differences from the source:
--   - encoding: the fixed integer n ≥ 4 of the proof of Theorem 5.2, chosen with 6/√n < ε → every natural number n ≥ 4; reason: the lemma does not involve ε and every n ≥ 4 meets 6/√n < ε for some ε > 0; the same instances
--   - generalization: a WBB DSIC and IR mechanism for F (value space unnamed) → every interval value space T ⊆ [0, ∞) containing q_0 and q_n = 1, and every DSIC, IR, WBB mechanism on T; reason: the support of F^n lies in [q_0, 1] ⊆ T, and the source argument only evaluates the mechanism on [q_0, 1]; T = [0, 1] is one instance, so the statement specializes to the source claim
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 5.8, inequality (29); §5.2; proof in Appendix A.13, printed p. 34 (PDF p. 35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_GeometricLaw
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 5.8, §5.2 p.34, inequality (29): for every integer `n ≥ 4`, `R = √n`,
`q_i = R^(i−n)`, every interval value space `T ⊆ ℝ≥0` containing `q_0` and
`q_n = 1`, and every DSIC, IR, WBB mechanism on `T` has
`Σ_{i=1}^n x(q_{i−1}, q_i) ≤ 5R` (the sum includes `i = 1`). -/
theorem lemma_5_8 (n : ℕ) (hn : 4 ≤ n) (T : Set ℝ) (hT0 : T ⊆ Set.Ici 0) (hT : T.OrdConnected)
    (hq0 : geomGrid n 0 ∈ T) (hq1 : (1 : ℝ) ∈ T) (M : SecondBestBT.Mechanism)
    (hM : IsMechanism T M) (hdsic : IsDSIC T M) (hir : IsIR T M) (hwbb : IsWBB T M) :
    ∑ i ∈ Finset.Icc 1 n, M.x (geomGrid n (i - 1), geomGrid n i) ≤ 5 * geomRatio n := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
