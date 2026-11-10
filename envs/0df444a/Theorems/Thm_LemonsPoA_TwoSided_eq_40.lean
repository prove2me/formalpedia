-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_eq_40
-- name    : LemonsPoA.TwoSided.eq_40
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:34.625657+00:00
-- url     : https://prove2.me/theorems/69d5f3b0-eb73-4198-8bad-04d08314bc98
-- title:
--   §4, Eq. (40) — for every forecast $d\ge0$: $R\ge\frac12\sqrt{\mathrm{Var}\,\hat v}\ge\frac{\sqrt{1+\rho}}{2\sqrt2}(d\sqrt{\mathrm{Var}\,x}+\sqrt{\mathrm{Var}\,y})$
-- statement:
--   Let $I$ be a market instance in which, under $\theta\sim G$, $(x(\theta),y(\theta))$ is log-concave (Definition 5.2 item 4, with the constant-coordinate clause), $x(\theta),y(\theta)$ are integrable, and $\mathrm{Corr}(x(\theta),y(\theta))\ge\rho>-1$ (item 5). For a forecast $d\ge 0$ let $\hat v=d\,x+y$, $\hat v_S=\hat v(\theta_S)$, $\hat v_B=\hat v(\theta_B)$ and $R=E[(\hat v_B-\hat v_S)_+]$. Then
--   $$\mathrm{Var}(\hat v_S)\ \ge\ \frac{1+\rho}{2}\Big(d\sqrt{\mathrm{Var}(x(\theta))}+\sqrt{\mathrm{Var}(y(\theta))}\Big)^2,$$
--   $$R\ \ge\ \frac12\sqrt{\mathrm{Var}(\hat v_S)}\ \ge\ \frac{\sqrt{1+\rho}}{2\sqrt2}\Big(d\sqrt{\mathrm{Var}(x(\theta))}+\sqrt{\mathrm{Var}(y(\theta))}\Big).$$
--
--   The correlation restriction prevents the two components of value from cancelling in the belief-robust market.
--
--   Differences from the source:
--   - reading: Definition 5.2 item 4: "$(x(\theta),y(\theta))$ has a log-concave density" → `LogConcavePrefs`: a joint log-concave Lebesgue density, or $x$ a.s. constant and $y$ with a log-concave density, or $y$ a.s. constant and $x$ with a log-concave density; reason: item 5 provides for a constant coordinate, which item 4 as printed excludes; Definition 1.4 item 1 (p. 10) states the clause (INSIGHTS I1)
--   - generalization: item 5: $\mathrm{Corr}(x,y)\ge\rho>-1$; "if either $x(\theta)$ or $y(\theta)$ is constant, then take this to be satisfied for $\rho=0$" → $-1<\rho\le\mathrm{Cov}(x,y)/(\sqrt{\mathrm{Var}\,x}\sqrt{\mathrm{Var}\,y})$ with the plain quotient, which is $0$ for a constant coordinate, so the condition reads $\rho\le 0$ there; reason: the paper's constant-coordinate case $\rho=0$ is included; allowing $-1<\rho<0$ adds instances. For (46) and (47) the conclusion is independent of $\rho$; for (40), (48), and Theorem 5.3 the bounds follow from the $\rho=0$ case by monotonicity (both sides of the second inequality in (48) share the positive factor $\sqrt{1+\rho}$)
--   - generalization: (40) is displayed for $d=E[C\mid\Sigma_S=\sigma^-_S]$ under Definition 4.1 → every $d\ge 0$, under items 4-5 of Definition 5.2 only; reason: p. 28 states that the derivation "applies to any nonnegative forecast $d$", and it uses only Lemma 4.4 and the correlation assumption; the paper's instances satisfy these hypotheses
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 24, §4, Eq. (40) (in the proof of Theorem 4.2; extended to every d ≥ 0 on p. 28)

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Market
import Definitions.Def_LemonsPoA_TwoSided_Distributions

open MeasureTheory ProbabilityTheory

namespace LemonsPoA.TwoSided

/-- §4, Eq. (40) (p. 24), for every nonnegative forecast `d` (p. 28): under items 4–5 of
Definition 5.2, `Var(v̂) ≥ ((1+ρ)/2)(d √Var x + √Var y)²` and
`R ≥ (1/2) √Var(v̂) ≥ (√(1+ρ)/(2√2)) (d √Var x + √Var y)`, where `v̂ = d x + y`. -/
theorem eq_40 {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
    (M : Market Θ SS SB) (hlc : LogConcavePrefs M.G M.x M.y)
    (hx : Integrable M.x M.G) (hy : Integrable M.y M.G)
    (ρ : ℝ) (hρ : -1 < ρ) (hcorr : ρ ≤ corr M.G M.x M.y) (d : ℝ) (hd : 0 ≤ d) :
    (1 + ρ) / 2 * (d * Real.sqrt (variance M.x M.G) + Real.sqrt (variance M.y M.G)) ^ 2 ≤
        variance (M.vhat d) M.G ∧
      1 / 2 * Real.sqrt (variance (M.vhat d) M.G) ≤ M.R d ∧
      Real.sqrt (1 + ρ) / (2 * Real.sqrt 2) *
          (d * Real.sqrt (variance M.x M.G) + Real.sqrt (variance M.y M.G)) ≤ M.R d := by sorry

end LemonsPoA.TwoSided
