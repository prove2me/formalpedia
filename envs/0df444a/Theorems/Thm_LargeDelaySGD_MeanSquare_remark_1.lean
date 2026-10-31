-- Prove2me | Theorems.Thm_LargeDelaySGD_MeanSquare_remark_1
-- name    : LargeDelaySGD.MeanSquare.remark_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:31.264141+00:00
-- url     : https://prove2.me/theorems/f8f80eb4-a52c-4818-a7df-fa5a8c0adfda
-- title:
--   Remark 1, p. 5 — under Assumption 1, E‖∇F‖ < ∞, f is differentiable with ∇f = E[∇F], and ∇f is L-Lipschitz
-- statement:
--   Let $F:\mathbb R^d\times\Xi\to\mathbb R$ satisfy Assumption 1 on the probability space $(\Xi,\mu)$, with second-moment bound $B$ and Lipschitz constant $L$ of $x\mapsto\mathbb E[\nabla F(x;\xi)]$, and let $f(x)=\mathbb E[F(x;\xi)]$. Then:
--   1. $\nabla F(x;\cdot)$ is integrable for every $x$, i.e. $\mathbb E\|\nabla F(x;\xi)\|_2<\infty$;
--   2. $f$ is differentiable at every $x$, with
--   $$\nabla f(x)=\mathbb E[\nabla F(x;\xi)];$$
--   3. $\nabla f$ is $L$-Lipschitz, i.e. $f$ is $L$-smooth.
--
--   This is the interchange of gradient and expectation that turns the stochastic gradient into an unbiased estimate of $\nabla f$; every later statement uses it.
--
--   **Formalization Note.** The paper attributes this to dominated convergence. The second-moment bound alone does not dominate difference quotients; the statement is posed as a claim about the formal model of Assumption 1 (which includes joint measurability of $\nabla F$), not about the paper's argument.
-- source:
--   Z. Zhou, P. Mertikopoulos, N. Bambos, P. W. Glynn, Y. Ye, Distributed Stochastic Optimization with Large Delays, arXiv:2107.02919v1, p. 5, Remark 1

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

namespace LargeDelaySGD.MeanSquare

open MeasureTheory ProbabilityTheory

theorem remark_1 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L) :
    (∀ x, Integrable (stochGrad F x) μ) ∧
      (∀ x, HasGradientAt (objective F μ) (∫ ξ, stochGrad F x ξ ∂μ) x) ∧
      LipschitzWith L (gradient (objective F μ)) := by sorry

end LargeDelaySGD.MeanSquare
