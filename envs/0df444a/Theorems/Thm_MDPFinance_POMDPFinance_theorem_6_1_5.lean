-- Prove2me | Theorems.Thm_MDPFinance_POMDPFinance_theorem_6_1_5
-- name    : MDPFinance.POMDPFinance.theorem_6_1_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:37:59.488813+00:00
-- url     : https://prove2.me/theorems/3e37df8d-76f3-45cd-90b7-1c7c8a349200
-- title:
--   Theorem 6.1.5 — partial vs. complete observation: which invests more in the risky asset
-- statement:
--   This theorem compares the optimal invested fraction under partial observation of the
--   up-probability $\theta$ against the fraction an investor who is simply told the posterior mean
--   $\bar\rho := \int\theta\,\rho(d\theta)$ would choose (the "complete observation" benchmark,
--   $\rho$ replaced by the degenerate belief $\delta_{\bar\rho}$). For $0<\gamma<1$ the partially
--   informed investor invests *more* in the risky asset than the complete-observation benchmark;
--   for $\gamma<0$ the comparison reverses. The book's own heuristic: risk aversion (the Arrow-Pratt
--   coefficient $(1-\gamma)/x$) decreases with $\gamma$, and the two regimes see the effect of
--   residual uncertainty about $\theta$ pull the optimal fraction in opposite directions relative to
--   its certainty-equivalent value.
--
--   **Formalization Note.** The optimal fractions $\alpha$ (at the true posterior) and $\alpha_{\bar
--   \rho}$ (at the degenerate belief) are characterized as *any* maximizers of the respective
--   one-step objectives (`IsOptimalFraction`, continuation values instantiated via `dPow`/the actual
--   Bayes update `Phi`), rather than through the explicit closed-form solution the book's own proof
--   derives via a separate result (Lemma 4.2.9, from a different chunk's own machinery unavailable
--   here): the comparison inequality is a fact about any maximizer of this one-variable concave
--   problem, independent of which closed form is used to exhibit it.
--
--   **Moderation note.** The continuation values are those of the binomial recursion (6.4) with $\tilde A=[0,1]$ (`dBin`), the market is `IsBinomialMarket`, $\bar\rho$ is the mean of the normalized posterior, and $0<d$, $\gamma\ne 0$, $p_0$ a prior density are hypotheses. The draft's $\bar\rho$ was $\int\theta\,\rho(\theta)d\theta$ for an unnormalized density, and its continuation values came from the general recursion (6.3).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 180, Theorem 6.1.5

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_Binomial
import Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- Theorem 6.1.5 (Bäuerle–Rieder, p. 180, PDF 193), for the binomial market with unknown
up-probability. For all `k` (stages remaining) and `\rho \in D_{Q_0}` it holds: `\alpha_k^*(\rho)
\ge \alpha_k^*(\bar\rho)` if `0 < \gamma < 1`, `\alpha_k^*(\rho) \le \alpha_k^*(\bar\rho)` if
`\gamma < 0`, where `\bar\rho := \int\theta\,\rho(d\theta) \in (0,1)` and `\alpha_k^*(\bar\rho)` is
the optimal fraction at the degenerate (Dirac-at-`\bar\rho`) belief, i.e. the complete-observation
case; `\bar u := u/(1+i)-1`, `\bar d := d_{\text{n}}/(1+i)-1` (down-factor named `dn` to avoid
clashing with the risky-asset dimension `d`). `α`/`αbar` are characterized as *any* maximisers of
the respective one-step problems (`IsOptimalFraction`, its continuation values instantiated via
the binomial recursion (6.4) `dBin`/`Fd.Phi` at the actual posterior `measureOfDensity rho`
resp. the degenerate belief `Measure.dirac \bar ρ`) rather than the closed form `\alpha^*(\lambda)`
the book's own proof derives (Lemma 4.2.9, a different, unavailable chunk) — see
`Def_..._Binomial.lean`'s docstring. The market is the binomial market (`IsBinomialMarket`,
`0 < d < 1+i < u`), `p_0` a prior density, and `\bar ρ = \int θ ρ(dθ)` is computed from the
normalized posterior. -/
theorem theorem_6_1_5 (M : FilterMarket ℝ 1) (Fd : FilterOp M) (u dn i γ : ℝ) (hdn : 0 < dn)
    (hd : dn < 1 + i) (hi : 1 + i < u) (hM : IsBinomialMarket M u dn i) (hγ : γ ≠ 0)
    (p0 : ℝ → ℝ) (hp0 : IsPriorDensity p0) (rho : ℝ → ℝ) (hrho : rho ∈ DQ0 p0) (k : ℕ)
    (α αbar : ℝ)
    (hα : IsOptimalFraction u dn i γ
        (dBin M Fd u dn i γ k (Fd.Phi (measureOfDensity rho) (ubar u i)))
        (dBin M Fd u dn i γ k (Fd.Phi (measureOfDensity rho) (dbar dn i)))
        (rhobar (measureOfDensity rho)) α)
    (hαbar : IsOptimalFraction u dn i γ
        (dBin M Fd u dn i γ k (Fd.Phi (Measure.dirac (rhobar (measureOfDensity rho))) (ubar u i)))
        (dBin M Fd u dn i γ k (Fd.Phi (Measure.dirac (rhobar (measureOfDensity rho))) (dbar dn i)))
        (rhobar (measureOfDensity rho)) αbar) :
    (0 < γ → γ < 1 → αbar ≤ α) ∧ (γ < 0 → α ≤ αbar) := by sorry

end MDPFinance.POMDPFinance
