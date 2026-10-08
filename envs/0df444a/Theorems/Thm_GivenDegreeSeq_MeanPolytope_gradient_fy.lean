-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_gradient_fy
-- name    : GivenDegreeSeq.MeanPolytope.gradient_fy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:46.456042+00:00
-- url     : https://prove2.me/theorems/d379d77c-ce8b-459c-9342-875880df419f
-- title:
--   Proof of Theorem 1.4, p. 16 — ∇f_y(x) = y − g(x)
-- statement:
--   For $y,x\in\mathbb R^n$ let
--   $$f_y(x)=\sum_{i=1}^n x_iy_i-\log\prod_{1\le i<j\le n}\big(1+e^{x_i+x_j}\big),\qquad g_i(x)=\sum_{j\neq i}\frac{e^{x_i+x_j}}{1+e^{x_i+x_j}}.$$
--   Then for every $x\in\mathbb R^n$ the gradient of $f_y$ is
--   $$\nabla f_y(x)=y-g(x).$$
--
--   Combined with Lemma 3.1 and the bound $f_y\le 0$ on $\operatorname{conv}(\mathcal D)$, this identity shows that every $y\in\operatorname{conv}(\mathcal D)$ is a limit of points $g(x_k)$ of $\mathcal R$.
--
--   **Formalization Note** The gradient is taken on `EuclideanSpace ℝ (Fin n)`, so $y-g(x)$, computed in `Fin n → ℝ`, is transported back to Euclidean space. The logarithm of the product is the paper's intended reading of the printed $\log\sum$ (p. 15).
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 16, proof of Theorem 1.4

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, proof of Theorem 1.4, p. 16: `∇f_y(x) = y − g(x)`,
the gradient taken on Euclidean space `EuclideanSpace ℝ (Fin n)`. -/
theorem gradient_fy {n : ℕ} (y : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun z : EuclideanSpace ℝ (Fin n) => fy y z.ofLp) x = WithLp.toLp 2 (y - g x.ofLp) := by sorry

end GivenDegreeSeq.MeanPolytope
