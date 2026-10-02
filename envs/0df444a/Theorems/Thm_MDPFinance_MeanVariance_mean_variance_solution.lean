-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_mean_variance_solution
-- name    : MDPFinance.MeanVariance.mean_variance_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:46.447264+00:00
-- url     : https://prove2.me/theorems/7aa05260-f37d-46db-8894-1827e6ddf655
-- title:
--   Theorem 4.6.6 — explicit solution of the mean-variance problem (MV) [GOAL]
-- statement:
--   With $(d_n)$ as in Eq. (4.34): a) the value of (MV) is
--   $$\mathrm{Var}_{x_0}^{\pi^*}[X_N] = \frac{d_0}{1-d_0}\big(\mathbb{E}_{x_0}^{\pi^*}[X_N] -
--   x_0S^0_N\big)^2, \qquad \mathbb{E}_{x_0}^{\pi^*}[X_N] = \mu;$$
--   b) the optimal portfolio strategy $\pi^*=(f_0^*,\dots,f_{N-1}^*)$ is
--   $$f_n^*(x) = \Big(\frac{\mu-d_0x_0S^0_N}{1-d_0}\cdot\frac{S^0_n}{S^0_N} - x\Big)\,
--   C_{n+1}^{-1}\,\mathbb{E}[R_{n+1}], \qquad x\in E.$$
--
--   This is the goal of the mission: the payoff of the Lagrangian-embedding technique built across
--   Lemmas 4.6.1-4.6.4 and Theorem 4.6.5. Mean-variance portfolio selection is not a standard
--   expected-utility Markov Decision Problem — the variance term is not linear in the underlying
--   probability measure, so no Bellman equation for it exists directly. The book's route embeds (MV)
--   into the tractable quadratic problem $QP(b)$ via a Lagrange multiplier and a saddle-point
--   argument, then specializes Theorem 4.6.5's closed form at the multiplier $\lambda^* =
--   (\mu-x_0S^0_N)d_0/(1-d_0)$, i.e. $b^*=\mu+\lambda^*$, to get this theorem's explicit frontier
--   and feedback policy.
--
--   **Formalization Note.** A formalization that solved (MV) by applying chunk `02a`'s Structure
--   Theorem directly to the variance objective — skipping the Lagrangian embedding entirely — would
--   not prove what this theorem proves (and would not even typecheck as a faithful Bellman equation,
--   since $\mathrm{Var}_{x_0}^\pi[X_N]$ has no such recursion); `mean_variance_solution` is stated
--   purely in terms of `IsOptimalMV`, `varXN` and `meanXN` from `MVMarket`, deliberately independent
--   of any intermediate Bellman value function, so that only the actual saddle-point route (via
--   `saddle_point_value`, `plambda_implies_qp`, `qp_solution`) can discharge it.
--
--   **Formalization Note (moderation).** $0<d_0<1$ is Lemma 4.6.4 under the model's Assumption
--   (FM), not an extra hypothesis.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 123, PDF 137, Theorem 4.6.6

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.6.6 (Bäuerle–Rieder, p. 123, PDF 137) — the goal of this mission. Let `(d_n)` be
as in Eq. (4.34). For the mean-variance problem `(MV)` (under the section's standing Assumption
(FM), carried by the model): a) the value is
`Var^{π^*}_{x_0}[X_N] = (d_0/(1-d_0))(𝔼^{π^*}_{x_0}[X_N] - x_0S⁰_N)^2`, and
`𝔼^{π^*}_{x_0}[X_N] = μ`; b) the optimal portfolio strategy `π^* = (f_0^*,…,f_{N-1}^*)` is
`f_n^*(x) = ((μ-d_0x_0S⁰_N)/(1-d_0) · S⁰_n/S⁰_N - x) C_{n+1}^{-1}𝔼[R_{n+1}]`. -/
theorem mean_variance_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))) :
    ∃ πstar : ℕ → ℝ → (Fin d → ℝ), M.IsOptimalMV πstar ∧
      M.varXN πstar = (dseq 0 / (1 - dseq 0)) * (M.meanXN πstar - M.x0 * M.S0 M.N) ^ 2 ∧
      M.meanXN πstar = M.μ ∧
      (∀ n < M.N, ∀ x : ℝ, πstar n x =
        fun k => ((M.μ - dseq 0 * M.x0 * M.S0 M.N) / (1 - dseq 0) * (M.S0 n / M.S0 M.N) - x) *
          ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k)) := by sorry

end MDPFinance.MeanVariance
