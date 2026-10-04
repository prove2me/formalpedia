-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_mean_risk_solution_plq
-- name    : MDPFinance.MeanVariance.mean_risk_solution_plq
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:26.216985+00:00
-- url     : https://prove2.me/theorems/4447db05-bfa4-4296-8576-c9d806c226de
-- title:
--   Theorem 4.7.4 — explicit solution of the mean-risk problem (MR), case $p<q$
-- statement:
--   Suppose $p<q$. With $\gamma_1 := \frac{q^N-p^N}{q^N}$, $\gamma_2 :=
--   \frac{(1-p)^N(q^N-p^N)}{\big((1-p)q\big)^N-\big((1-q)p\big)^N}$, $\lambda^* := \min\Big(
--   \frac{(1-q)^N}{(1-p)^N-(1-q)^N}, \frac{p^N(1-\gamma)^{-1}-q^N}{q^N-p^N}\Big)$: a) the value of
--   (MR) is given by the same formula as Theorem 4.7.3, with these $\lambda^*,\gamma_1$; b) the
--   optimal policy $\pi^*=(f^*,\dots,f^*)$ is stationary, with
--   $$f^*(x) = \begin{cases} \dfrac{1}{1-d}\Big((\mu-x_0)\dfrac{q^N}{p^N-q^N} - x_0+x\Big) &
--   \gamma_1\le\gamma\le\gamma_2 \\[6pt] \dfrac{1}{1-u}\Big((x_0-\mu)
--   \dfrac{(1-q)^N}{(1-q)^N-(1-p)^N} - x_0+x\Big) & \gamma\ge\gamma_2. \end{cases}$$
--
--   The book's own remark: "for the sake of completeness we will present the solution of problem (MR)
--   also in the case $p<q$", with new constants $\gamma_1,\gamma_2,\lambda^*$ but the *same* two
--   feedback-rule formulas as Theorem 4.7.3, now attached to swapped case conditions.
--
--   **Formalization Note.** A distinct item from `mean_risk_solution`, not a corollary derived from
--   it by symmetry, since the book itself restates the whole theorem with new constants rather than
--   deriving this case from the $p>q$ one.
--
--   **Formalization Note (moderation).** Part (b) is stated case by case: the first formula is
--   optimal when $\gamma\ge\gamma_2$, the second when $\gamma_1\le\gamma\le\gamma_2$ (both at
--   $\gamma=\gamma_2$); the draft asserted the existence of an optimal policy unconditionally,
--   which fails when $\gamma<\gamma_1$ (value $-\infty$).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 131, PDF 145, Theorem 4.7.4

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.7.4 (Bäuerle–Rieder, p. 131, PDF 145), `p < q` case, under the section's standing
assumptions. With `γ_1 := (q^N-p^N)/q^N`, `γ_2 := (1-p)^N(q^N-p^N)/(((1-p)q)^N-((1-q)p)^N)`,
`λ^* := min((1-q)^N/((1-p)^N-(1-q)^N), (p^N(1-γ)^{-1}-q^N)/(q^N-p^N))`: a) the value of `(MR)`
is the same formula as in Theorem 4.7.3, with these `λ^*`, `γ_1`; b) the optimal policy `π^*` is
stationary, `π^* = (f^*,…,f^*)`, with `f^*(x) = (1/(1-d))((μ-x_0)q^N/(p^N-q^N) - x_0 + x)` if
`γ_1 ≤ γ ≤ γ_2`, and `f^*(x) = (1/(1-u))((x_0-μ)(1-q)^N/((1-q)^N-(1-p)^N) - x_0 + x)` if
`γ ≥ γ_2`. -/
theorem mean_risk_solution_plq {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.p < M.q) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = (M.q ^ M.N - M.p ^ M.N) / M.q ^ M.N)
    (hγ2 : γ2 = (1 - M.p) ^ M.N * (M.q ^ M.N - M.p ^ M.N) /
      (((1 - M.p) * M.q) ^ M.N - ((1 - M.q) * M.p) ^ M.N))
    (hlamstar : lamstar = min ((1 - M.q) ^ M.N / ((1 - M.p) ^ M.N - (1 - M.q) ^ M.N))
      ((M.p ^ M.N * (1 - M.γ)⁻¹ - M.q ^ M.N) / (M.q ^ M.N - M.p ^ M.N))) :
    (M.γ ≥ γ1 → M.VMR = (((M.μ - M.x0) * lamstar - M.x0 : ℝ) : EReal)) ∧
      (¬ M.γ ≥ γ1 → M.VMR = ⊥) ∧
      (γ1 ≤ M.γ → M.γ ≤ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.d)⁻¹ * ((M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0 + x))) ∧
      (M.γ ≥ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.u)⁻¹ * ((M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) -
          M.x0 + x))) := by sorry

end MDPFinance.MeanVariance
