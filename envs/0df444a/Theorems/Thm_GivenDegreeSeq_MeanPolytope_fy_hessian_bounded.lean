-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_fy_hessian_bounded
-- name    : GivenDegreeSeq.MeanPolytope.fy_hessian_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:28.737671+00:00
-- url     : https://prove2.me/theorems/0e5c8fc6-c8cb-4289-a32d-0305f8fc565e
-- title:
--   Proof of Theorem 1.4, p. 16 — f_y is twice differentiable and ∇²f_y is uniformly bounded
-- statement:
--   Fix $y\in\mathbb R^n$ and let
--   $$f_y(x)=\sum_{i=1}^n x_iy_i-\sum_{1\le i<j\le n}\log\big(1+e^{x_i+x_j}\big),\qquad x\in\mathbb R^n.$$
--   Then $f_y$ is twice differentiable on $\mathbb R^n$, and its Hessian is uniformly bounded: there is a finite constant $C$ such that
--   $$\big\|\nabla^2 f_y(x)\big\|_{\mathrm{op}}\le C\qquad\text{for all }x\in\mathbb R^n,$$
--   where $\|\cdot\|_{\mathrm{op}}$ is the $L^2$ operator norm.
--
--   The paper asserts this as "easy to show"; it is the hypothesis that allows Lemma 3.1 to be applied to $f_y$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $f_y$ is composed with the identification of Euclidean space with `Fin n → ℝ`. Twice differentiable means that $f_y$ and its Fréchet derivative are differentiable; the Hessian is the second Fréchet derivative, whose norm as a continuous bilinear map equals the $L^2$ operator norm of the Hessian matrix. The differentiability conjuncts are implicit in the paper's sentence and are added so that the statement matches the hypotheses of Lemma 3.1.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 16, proof of Theorem 1.4 ("it is easy to show that ∇²f is uniformly bounded")

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, proof of Theorem 1.4, p. 16: "it is easy to show
that ∇²f is uniformly bounded". For every `y`, the function `f_y`, viewed on Euclidean space
`EuclideanSpace ℝ (Fin n)`, is twice differentiable and the operator norm of its second derivative
(the L² operator norm of its Hessian) is bounded uniformly in `x`. -/
theorem fy_hessian_bounded {n : ℕ} (y : Fin n → ℝ) :
    Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin n) => fy y x.ofLp) ∧
      Differentiable ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => fy y x.ofLp)) ∧
        ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n),
          ‖fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => fy y x.ofLp)) x‖ ≤ C := by sorry

end GivenDegreeSeq.MeanPolytope
