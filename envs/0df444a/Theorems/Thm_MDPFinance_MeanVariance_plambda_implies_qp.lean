-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_plambda_implies_qp
-- name    : MDPFinance.MeanVariance.plambda_implies_qp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:07:27.174269+00:00
-- url     : https://prove2.me/theorems/4d6bcc32-7cae-4c74-81fb-8cec411e9515
-- title:
--   Lemma 4.6.3 — optimality for P(lambda) implies optimality for QP(b)
-- statement:
--   If $\pi^*$ is optimal for $P(\lambda)$ (minimizes the Lagrangian
--   $L_{x_0}(\cdot,\lambda)$), then $\pi^*$ is also optimal for $QP(b)$ with
--   $b := \mathbb{E}_{x_0}^{\pi^*}[X_N] + \lambda$.
--
--   This reduces solving $P(\lambda)$ — whose objective mixes a variance and a linear term, and is
--   not directly tractable by dynamic programming — to solving the auxiliary quadratic-cost problem
--   $QP(b)$, whose Bellman recursion Theorem 4.6.5 solves in closed form.
--
--   **Formalization Note.** None; a direct restatement of the book's `Prop` with $b$ named explicitly
--   as $\mathbb{E}_{x_0}^{\pi^*}[X_N]+\lambda$, matching the book's own definition of $b$ in the
--   statement.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 120, PDF 134, Lemma 4.6.3

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Lemma 4.6.3 (Bäuerle–Rieder, p. 120, PDF 134). If `π*` is optimal for `P(λ)`, then `π*` is
optimal for `QP(b)` with `b := 𝔼^{π*}_{x_0}[X_N] + λ`. -/
theorem plambda_implies_qp {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (lam : ℝ)
    (πstar : ℕ → ℝ → (Fin d → ℝ)) (hopt : M.IsOptimalPLambda lam πstar) :
    M.IsOptimalQP (M.meanXN πstar + lam) πstar := by sorry

end MDPFinance.MeanVariance
