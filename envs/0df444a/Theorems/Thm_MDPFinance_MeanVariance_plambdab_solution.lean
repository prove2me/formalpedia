-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_plambdab_solution
-- name    : MDPFinance.MeanVariance.plambdab_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:55.712991+00:00
-- url     : https://prove2.me/theorems/0c66035a-e348-4cc3-a9da-acf33a61cba1
-- title:
--   Theorem 4.7.1 — explicit solution of the auxiliary problem P(lambda,b)
-- statement:
--   With $c_n,d_n$ as in Eq. defining `MRcdSeq`: a) if $c_0\ge d_0$, the value functions are
--   $V_n(x) = c_n(x+b)^- - d_n(x+b)^+$ and $V_0(x_0)$ is the value of $P(\lambda,b)$; if $c_0<d_0$,
--   the value of $P(\lambda,b)$ is $-\infty$. b) If $c_0\ge d_0$, the optimal policy
--   $\pi^*=(f_0^*,\dots,f_{N-1}^*)$ is stationary,
--   $$f_n^*(x) = f^*(x) := \max\Big(\frac{x+b}{1-u}, \frac{x+b}{1-d}\Big), \qquad x\in E.$$
--
--   This is $P(\lambda,b)$'s own Bellman solution via the Structure Assumption (SAN), with value
--   class $\{v(x)=c(x+b)^--d(x+b)^+\}$ and feedback class $\{f(x)=\max(c_1(x+b),c_2(x+b))\}$; it
--   is the building block Proposition 4.7.2 specializes to solve $P(\lambda)$.
--
--   **Formalization Note.** The book's Remark 2.3.14/Theorem 2.5.4 aside — that the strong
--   Integrability Assumption (AN) fails here but the weaker Theorem 2.5.4 still applies — is proof
--   machinery, not part of the numbered statement, and is not restated as a hypothesis.
--
--   **Formalization Note (moderation).** $p>q$ (Assumption (FM)(ii)) is carried: the proof's
--   equivalence $c_0\ge d_0 \iff c_n\ge d_n$ for all $n$ rests on it.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 126-127, PDF 140-141, Theorem 4.7.1

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_MDPFinance_MeanVariance_PLambdaBValueFunction
import Definitions.Def_MDPFinance_MeanVariance_MRcdSeq

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.7.1 (Bäuerle–Rieder, p. 126, PDF 140), under the section's standing assumptions
(`d < 1 < u`, `0 < x0 < μ` in the model; (FM)(ii) `p > q`, `hpq`). With `c_n, d_n` as in
`MRcdSeq`: a) if `c_0 ≥ d_0`, the value functions are `V_n(x) = c_n(x+b)^- - d_n(x+b)^+`, and
`V_0(x_0)` is the value of `P(λ,b)`; if `c_0 < d_0`, the value of `P(λ,b)` is `-∞`. b) if
`c_0 ≥ d_0`, the optimal policy `π^* = (f_0^*,…,f_{N-1}^*)` is stationary,
`f_n^*(x) = f^*(x) := max((x+b)/(1-u), (x+b)/(1-d))`. -/
theorem plambdab_solution {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.q < M.p) (lam b : ℝ) (hlam : 0 ≤ lam) :
    (M.cSeq lam 0 ≥ M.dSeq lam 0 →
      (∀ n ≤ M.N, ∀ x : ℝ,
        M.VPlambdabFrom lam b n x = ((M.cSeq lam n * max (-(x + b)) 0) -
          M.dSeq lam n * max (x + b) 0 : EReal)) ∧
      (∃ πstar : ℕ → ℝ → ℝ, M.IsAdmissible 0 πstar ∧
        (∀ n < M.N, ∀ x : ℝ, πstar n x = max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d))) ∧
        M.IsOptimalPlambdab lam b πstar)) ∧
      (M.cSeq lam 0 < M.dSeq lam 0 → M.VPlambdab lam b = ⊥) := by sorry

end MDPFinance.MeanVariance
