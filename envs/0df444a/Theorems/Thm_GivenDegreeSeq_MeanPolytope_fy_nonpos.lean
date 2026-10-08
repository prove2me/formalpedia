-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_fy_nonpos
-- name    : GivenDegreeSeq.MeanPolytope.fy_nonpos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:28.869852+00:00
-- url     : https://prove2.me/theorems/5c0a8a1b-6041-4982-a24a-8437c1aef251
-- title:
--   Proof of Theorem 1.4, p. 16 — f_y(x) ≤ 0 for all y ∈ conv(D) and x ∈ ℝⁿ
-- statement:
--   For $y,x\in\mathbb R^n$ let
--   $$f_y(x)=\sum_{i=1}^n x_iy_i-\log\prod_{1\le i<j\le n}\big(1+e^{x_i+x_j}\big).$$
--   Let $\mathcal D$ be the set of degree sequences of simple graphs on $n$ vertices. Then
--   $$f_y(x)\le 0\qquad\text{for all } y\in\operatorname{conv}(\mathcal D),\ x\in\mathbb R^n.$$
--
--   Together with Lemma 3.1, this bound is what forces the gradient of $f_y$ to come arbitrarily close to $0$, which proves the hard inclusion $\operatorname{conv}(\mathcal D)\subseteq\overline{\mathcal R}$ of Theorem 1.4.
--
--   **Formalization Note** The paper prints $\log\sum_{1\le i<j\le n}(1+e^{x_i+x_j})$ in the definition of $f_y$ on p. 15. The product used here is the reading under which "taking logs, we get $f_d(x)\le 0$" (p. 16) follows from the probability formula and $\nabla f_y=y-g$ holds; with the printed sum the claim is false: for $n=3$, the degree sequence $y=(2,2,2)$ of the triangle and $x=(t,t,t)$, the printed expression equals $6t-\log\big(3(1+e^{2t})\big)$, which tends to $+\infty$ as $t\to\infty$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 16, proof of Theorem 1.4 (f_y defined on p. 15)

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, proof of Theorem 1.4, p. 16:
`f_y(x) ≤ 0` for all `y ∈ conv(D)` and `x ∈ ℝⁿ`, where
`f_y(x) = Σ_i x_i y_i − log ∏_{i<j}(1 + e^{x_i+x_j})`. -/
theorem fy_nonpos {n : ℕ} :
    ∀ y ∈ convexHull ℝ (D n), ∀ x : Fin n → ℝ, fy y x ≤ 0 := by sorry

end GivenDegreeSeq.MeanPolytope
