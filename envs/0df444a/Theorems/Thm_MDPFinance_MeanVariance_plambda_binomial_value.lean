-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_plambda_binomial_value
-- name    : MDPFinance.MeanVariance.plambda_binomial_value
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:07.905982+00:00
-- url     : https://prove2.me/theorems/4b8b4565-4030-44c3-a375-533486d6fc74
-- title:
--   Proposition 4.7.2 — binomial-model value of the auxiliary problem P(lambda)
-- statement:
--   With $\gamma_1 := 1-\big(\frac{1-p}{1-q}\big)^N$, $\gamma_2 := \frac{p^N\big((1-q)^N
--   -(1-p)^N\big)}{\big(p(1-q)\big)^N-\big(q(1-p)\big)^N}$, $\lambda^* := \min\Big(
--   \frac{q^N}{p^N-q^N}, \frac{(1-p)^N(1-\gamma)^{-1}-(1-q)^N}{(1-q)^N-(1-p)^N}\Big)$: a) the value
--   of $P(\lambda)$ is $(\mu-x_0)\lambda - x_0$ if $\lambda\in[0,\lambda^*]$ and $\gamma\ge
--   \gamma_1$, and $-\infty$ otherwise; b) the optimal policy $\pi^*$ for $P(\lambda)$ is
--   stationary, $\pi^*=(f^b,\dots,f^b)$, with $b=-x_0$ for $\lambda\in[0,\lambda^*)$,
--   $b\in[-x_0,\infty)$ if $\lambda=\lambda^*$ and $\gamma\ge\gamma_2$, and $b\in(-\infty,
--   -x_0]$ if $\lambda=\lambda^*$ and $\gamma_1\le\gamma\le\gamma_2$.
--
--   Obtained from Theorem 4.7.1 by minimizing over $b$, using that $V^b_0(x_0)=-\infty$ exactly when
--   $\lambda$ exceeds a threshold $\lambda_1^*(\gamma)$; this is the last step before assembling
--   $(MR)$'s own solution via the outer supremum over $\lambda\ge0$.
--
--   **Formalization Note.** Feasibility of the value (finiteness) is stated via a plain existential
--   `¬∃ v, ... = v` rather than `≠ ⊥` on the `EReal` infimum, since the book's own $-\infty$ outcome
--   is exactly the infimum failing to be any real value; part b)'s case split matches the book's own
--   three-way split on $\lambda,\gamma$ exactly.
--
--   **Formalization Note (moderation).** The $-\infty$ case is stated as the extended-real
--   infimum being $-\infty$. Part (b) is stated for the finite-value case $\gamma\ge\gamma_1$ (no
--   optimal policy exists when the value is $-\infty$) and reads the book's "$b\in\dots$" as: each
--   such $b$ gives an optimal stationary policy $(f^b,\dots,f^b)$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 128-129, PDF 142-143, Proposition 4.7.2

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_MDPFinance_MeanVariance_MRcdSeq

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Proposition 4.7.2 (Bäuerle–Rieder, p. 129, PDF 143), the binomial-model value of `P(λ)`
(`p > q`, under the section's standing assumptions). With `γ_1 := 1-((1-p)/(1-q))^N`,
`γ_2 := p^N((1-q)^N-(1-p)^N)/((p(1-q))^N - (q(1-p))^N)`,
`λ^* := min(q^N/(p^N-q^N), ((1-p)^N(1-γ)^{-1}-(1-q)^N)/((1-q)^N-(1-p)^N))`: a) the value of `P(λ)`
is `(μ-x_0)λ - x_0` if `λ ∈ [0,λ^*]` and `γ ≥ γ_1`, else `-∞`; b) the optimal policies `π^*` for
`P(λ)` are stationary, `π^* = (f^b,…,f^b)` with `f^b(x) = max((x+b)/(1-u), (x+b)/(1-d))`, where
`b = -x_0` if `λ ∈ [0,λ^*)`, `b ∈ [-x_0,∞)` if `λ = λ^*` and `γ ≥ γ_2`, `b ∈ (-∞,-x_0]` if
`λ = λ^*` and `γ_1 ≤ γ ≤ γ_2` (each such `b` giving an optimal policy, in the finite-value case
`γ ≥ γ_1`). -/
theorem plambda_binomial_value {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)))
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ((lam ∈ Set.Icc (0 : ℝ) lamstar ∧ M.γ ≥ γ1 →
        (⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) =
          (((M.μ - M.x0) * lam - M.x0 : ℝ) : EReal)) ∧
      (¬ (lam ∈ Set.Icc (0 : ℝ) lamstar ∧ M.γ ≥ γ1) →
        (⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) = ⊥)) ∧
      (M.γ ≥ γ1 →
        (lam < lamstar →
          M.IsOptimalPLambda lam (fun _ x => max ((x + -M.x0) / (1 - M.u)) ((x + -M.x0) / (1 - M.d)))) ∧
        (lam = lamstar → M.γ ≥ γ2 → ∀ b, -M.x0 ≤ b →
          M.IsOptimalPLambda lam (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d)))) ∧
        (lam = lamstar → γ1 ≤ M.γ → M.γ ≤ γ2 → ∀ b, b ≤ -M.x0 →
          M.IsOptimalPLambda lam (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d))))) := by sorry

end MDPFinance.MeanVariance
