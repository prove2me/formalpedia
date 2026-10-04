-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_mean_risk_solution
-- name    : MDPFinance.MeanVariance.mean_risk_solution
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:45.589582+00:00
-- url     : https://prove2.me/theorems/0988a5b4-3ec8-4d87-a9dc-f968d3c1fd85
-- title:
--   Theorem 4.7.3 — explicit solution of the mean-risk problem (MR), case $p>q$
-- statement:
--   With $\gamma_1,\gamma_2,\lambda^*$ as in Proposition 4.7.2: a) the value of (MR) is
--   $V_{MR}(x_0) = (\mu-x_0)\lambda^*-x_0$ if $\gamma\ge\gamma_1$, and $-\infty$ otherwise; b)
--   the optimal policy $\pi^*=(f^*,\dots,f^*)$ is stationary, with
--   $$f^*(x) = \begin{cases} \dfrac{1}{1-d}\Big((\mu-x_0)\dfrac{q^N}{p^N-q^N} - x_0+x\Big) &
--   \gamma\ge\gamma_2 \\[6pt] \dfrac{1}{1-u}\Big((x_0-\mu)\dfrac{(1-q)^N}{(1-q)^N-(1-p)^N} -
--   x_0+x\Big) & \gamma_1\le\gamma\le\gamma_2. \end{cases}$$
--
--   This is §4.7's own capstone: (MR)'s value equals $\sup_{\lambda\ge0}\inf_\pi
--   L_{x_0}(\pi,\lambda)$, computed from Proposition 4.7.2's formula optimized over $\lambda$, and
--   Lemma 4.6.2's saddle-point argument (reused verbatim from the mean-variance section) then
--   transfers this to (MR)'s own $\inf$-$\sup$ value.
--
--   **Formalization Note.** Proved for the case $p>q$ (the book's standing Assumption (FM)(ii) for
--   this section); the companion case $p<q$ is Theorem 4.7.4, a separate item since the book gives it
--   different constants $\gamma_1,\gamma_2,\lambda^*$, not a corollary of this statement.
--
--   **Formalization Note (moderation).** Part (b) is stated case by case: the first formula is
--   optimal when $\gamma\ge\gamma_2$, the second when $\gamma_1\le\gamma\le\gamma_2$ (both at
--   $\gamma=\gamma_2$); the draft asserted the existence of an optimal policy unconditionally,
--   which fails when $\gamma<\gamma_1$ (value $-\infty$).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 130, PDF 144, Theorem 4.7.3

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.7.3 (Bäuerle–Rieder, p. 130, PDF 144), `p > q` case, under the section's standing
assumptions. With `γ_1, γ_2, λ^*` as in `plambda_binomial_value`: a) the value of `(MR)` is
`V_{MR}(x_0) = (μ-x_0)λ^*-x_0` if `γ ≥ γ_1`, else `-∞`; b) (for `γ ≥ γ_1`) the optimal policy
`π^*` is stationary, `π^* = (f^*,…,f^*)`, with `f^*(x) = (1/(1-d))((μ-x_0)q^N/(p^N-q^N) - x_0 + x)`
if `γ ≥ γ_2`, and `f^*(x) = (1/(1-u))((x_0-μ)(1-q)^N/((1-q)^N-(1-p)^N) - x_0 + x)` if
`γ_1 ≤ γ ≤ γ_2`. -/
theorem mean_risk_solution {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N))) :
    (M.γ ≥ γ1 → M.VMR = (((M.μ - M.x0) * lamstar - M.x0 : ℝ) : EReal)) ∧
      (¬ M.γ ≥ γ1 → M.VMR = ⊥) ∧
      (M.γ ≥ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.d)⁻¹ * ((M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0 + x))) ∧
      (γ1 ≤ M.γ → M.γ ≤ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.u)⁻¹ * ((M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) -
          M.x0 + x))) := by sorry

end MDPFinance.MeanVariance
