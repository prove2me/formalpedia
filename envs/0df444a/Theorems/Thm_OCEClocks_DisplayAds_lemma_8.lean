-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_8
-- name    : OCEClocks.DisplayAds.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:21:26.824297+00:00
-- url     : https://prove2.me/theorems/6297fb0f-093e-49b3-b023-0e3d1e9785ac
-- title:
--   Lemma 8 — first ages of disjoint intervals are negatively associated
-- statement:
--   Let $\lambda>0$ and consider the stationary Poisson process of rate $\lambda$ on $\mathbb R$. Let $I_1,\dots,I_n$ be pairwise disjoint intervals of finite positive length. Then the first ages
--
--   $$\widehat A(I_1),\ \dots,\ \widehat A(I_n)$$
--
--   are negatively associated (Definition 1).
--
--   Each clock of the First-Age Poisson generator is a nonincreasing function of the first age of its interval, so this lemma is the source of negative association in Lemma 9.
--
--   **Formalization Note** An interval of finite positive length is a set $I\subseteq\mathbb R$ that is order-connected (`Set.OrdConnected`), bounded, and of positive Lebesgue measure. Open, closed and half-open intervals are all allowed, anywhere on $\mathbb R$.
--
--   Differences from the source:
--   - encoding: intervals I_1, …, I_n of finite positive length → order-connected, bounded subsets of ℝ with positive Lebesgue measure, indexed by Fin n; reason: these are exactly the intervals with endpoints a < b in ℝ, of any openness
--   - encoding: a stationary rate-λ Poisson process on ℝ → the arrivals T_k built from i.i.d. Exp(λ) gaps (G_k)_{k∈ℤ} (T_1 = G_1, −T_0 = G_0, further gaps in both directions), under gapLaw λ; reason: this construction is the paper's own (p. 8) and has the law of the stationary process
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 8, Lemma 8

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_NegAssoc
import Definitions.Def_OCEClocks_DisplayAds_PoissonProcess

open MeasureTheory

namespace OCEClocks.DisplayAds

/-- Lemma 8 (p. 8): for pairwise disjoint intervals `I_1, …, I_n` of finite positive length, the
first ages `Â(I_1), …, Â(I_n)` of the stationary rate-`λ` Poisson process are negatively
associated. -/
theorem lemma_8 (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (I : Fin n → Set ℝ)
    (hconn : ∀ k, (I k).OrdConnected) (hbdd : ∀ k, Bornology.IsBounded (I k))
    (hpos : ∀ k, 0 < volume (I k)) (hdisj : Pairwise (Function.onFun Disjoint I)) :
    NegAssoc (gapLaw lam) (fun k G => firstAge G (I k)) := by sorry

end OCEClocks.DisplayAds
