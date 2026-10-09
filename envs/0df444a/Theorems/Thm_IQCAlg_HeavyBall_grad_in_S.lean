-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_grad_in_S
-- name    : IQCAlg.HeavyBall.grad_in_S
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:52.05443+00:00
-- url     : https://prove2.me/theorems/4f394e4f-94ec-40d0-adff-0bcef4416ae6
-- title:
--   (4.11), p. 23 — any f with gradient (4.11) lies in S(1, 25)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be differentiable with $f'(x)=\nabla f(x)$ for every $x$, where $\nabla f$ is the piecewise-linear map (4.11):
--   $$\nabla f(x)=\begin{cases}25x & x<1,\\ x+24 & 1\le x<2,\\ 25x-24 & x\ge 2.\end{cases}$$
--   Then $f\in S(1,25)$: $f$ is continuously differentiable, strongly convex with parameter $m=1$, and its derivative is Lipschitz with constant $L=25$.
--
--   This is the claim "It is easy to check that $\nabla f(x)$ is continuous and monotone, and so $f\in S(m,L)$ with $m=1$ and $L=25$" of Section 4.6. It shows that the counterexample function lies in the class for which the Heavy-ball tuning of Proposition 1 would be expected to work.
--
--   **Formalization Note** $f$ is any antiderivative of (4.11) (they differ by constants); the hypothesis is `HasDerivAt f (gradF x) x` at every point.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 23, (4.11) and the sentence after it

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- (4.11) claim, p. 23: every `f : ℝ → ℝ` whose derivative is the gradient (4.11) lies in
`S(1, 25)`. -/
theorem grad_in_S (f : ℝ → ℝ) (hf : ∀ x : ℝ, HasDerivAt f (gradF x) x) :
    InSmL1 f 1 25 := by sorry

end IQCAlg.HeavyBall
