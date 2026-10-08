-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_bias_bound
-- name    : GilesMLMC.Complexity.bias_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:41.030848+00:00
-- url     : https://prove2.me/theorems/f1bfa171-f9d1-4795-9f82-565f3bab3151
-- title:
--   Bias bound — $(E[\widehat Y]-E[P])^2\le\tfrac12\varepsilon^2$ from (i), (ii) and (6)
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space, $P$ and $\widehat P_l$ ($l\ge0$) integrable random variables, and $\widehat Y_l^{(n)}$ square-integrable level estimators for every sample size $n\ge1$, with $h_l=M^{-l}T$ and constants $\alpha,c_1$, such that
--
--   1. (i) $\big|E[\widehat P_l-P]\big|\le c_1h_l^\alpha$ for every $l$;
--   2. (ii) $E[\widehat Y_l^{(n)}]=E[\widehat P_0]$ if $l=0$ and $E[\widehat Y_l^{(n)}]=E[\widehat P_l-\widehat P_{l-1}]$ if $l>0$, for every $n\ge1$.
--
--   Let $\varepsilon>0$, $L\ge0$, sample sizes $N_l\ge1$, and assume $c_1h_L^\alpha\le\varepsilon/\sqrt2$ (the second inequality of (6)). Then the multilevel estimator $\widehat Y=\sum_{l=0}^L\widehat Y_l^{(N_l)}$ satisfies
--   $$\big(E[\widehat Y]-E[P]\big)^2\le\tfrac12\varepsilon^2 .$$
--
--   This is the bias half of the MSE bound: together with a $\tfrac12\varepsilon^2$ bound on the variance it gives $\mathrm{MSE}\le\varepsilon^2$.
--
--   **Formalization Note** $P$ and $\widehat P_l$ are arbitrary random variables; in the paper they come from an SDE and its discretisation, which the theorem uses only through (i)–(iv). This makes the statement more general, not weaker. Each hypothesis on $\widehat Y_l$ is assumed for every sample size $N\ge1$, because the proof chooses the sample sizes; $\widehat Y_l$ is assumed square integrable (Lean's `variance` is $0$ off $L^2$). Hypothesis (i) carries an absolute value: the page prints $E[\widehat P_l-P]\le c_1h_l^\alpha$, under which this bound is false; the proof uses the two-sided bound. Taking the second inequality of (6) as a hypothesis makes the statement independent of the ceiling; no condition on $M$, $T$, $\alpha$, $c_1$ is needed.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, directly after (6), p. 609

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup

namespace GilesMLMC.Complexity

/-- The bias bound (Giles 2008, §3, proof of Theorem 3.1, p. 609, PDF 3, right column, directly after (6)): because of properties (i) and (ii), `(E[Ŷ] − E[P])² ≤ ½ ε²`.

Formalization Note. `Y l n` is the level-`l` estimator Ŷ_l built from `n` samples; the paper's `P`, `P̂_l` come from an SDE and its discretisation, which the theorem uses only through (i)–(iv), so here they are arbitrary random variables (more general, not weaker). Hypotheses are assumed for every sample size `n ≥ 1` because the proof chooses the sample sizes; `MemLp 2` is needed because `variance` is 0 off L². Hypothesis (i) has an absolute value (the page prints the one-sided `E[P̂_l − P] ≤ c₁ h_l^α`, under which the bound is false). The second inequality of (6), `c₁ h_L^α ≤ ε/√2`, is taken as a hypothesis, so the statement holds for every level `L` and every choice of sample sizes `N_l ≥ 1`. -/
theorem bias_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (T : ℝ) (α c₁ ε : ℝ) (hε : 0 < ε)
    (P : Ω → ℝ) (Phat : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ)
    (hP : MeasureTheory.Integrable P μ)
    (hPhat : ∀ l, MeasureTheory.Integrable (Phat l) μ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_i : ∀ l, |∫ ω, (Phat l ω - P ω) ∂μ| ≤ c₁ * h M T l ^ α)
    (h_ii : ∀ l N, 1 ≤ N → ∫ ω, Y l N ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ)
    (L : ℕ) (N : ℕ → ℕ) (hN : ∀ l, 1 ≤ N l)
    (hL : c₁ * h M T L ^ α ≤ ε / Real.sqrt 2) :
    (∫ ω, estimator Y N L ω ∂μ - ∫ ω, P ω ∂μ) ^ 2 ≤ ε ^ 2 / 2 := by sorry

end GilesMLMC.Complexity
