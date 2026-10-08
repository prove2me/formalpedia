-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_lemma_3_1
-- name    : GivenDegreeSeq.MeanPolytope.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:41.301701+00:00
-- url     : https://prove2.me/theorems/82342222-0980-42f2-b9d4-bfb4e1ae6f81
-- title:
--   Lemma 3.1 — if f ≤ M and ‖∇²f‖ ≤ C, then |∇f(x)|² ≤ 2C(M − f(x)), so ∇f(x_k) → 0 along some sequence
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be twice differentiable and bounded above, and put
--   $$M:=\sup_{x\in\mathbb R^n}f(x)<\infty.$$
--   Suppose there is a finite constant $C$ such that the $L^2$ operator norm of the Hessian $\nabla^2 f(x)$ is at most $C$ for every $x$. Then for every $x\in\mathbb R^n$,
--   $$|\nabla f(x)|^2\le 2C\big(M-f(x)\big),$$
--   where $|\cdot|$ is the Euclidean norm. In particular, there is a sequence $(x_k)_{k\ge1}$ with $\lim_{k\to\infty}\nabla f(x_k)=0$.
--
--   The lemma says that a smooth function bounded above has approximate critical points even when it attains no maximum. In the proof of Theorem 1.4 it is applied to $f_y$ for $y\in\operatorname{conv}(\mathcal D)$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so the norm of the gradient is the Euclidean norm. Twice differentiable is stated as: $f$ is differentiable and its Fréchet derivative is differentiable. The Hessian bound is a bound on the norm of the second Fréchet derivative as a continuous bilinear map, which is the $L^2$ operator norm of the Hessian matrix. $M$ is the supremum of the range of $f$, which is genuine because the range is nonempty and bounded above. $C=0$ is allowed, as on the page. The sequence is indexed by $\mathbb N$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, pp. 14–15, Lemma 3.1

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

open Filter Topology

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, Lemma 3.1, pp. 14–15. Let `f : ℝⁿ → ℝ` be twice
differentiable with `M := sup f < ∞`, and let the L² operator norm of its Hessian be bounded by `C`
everywhere. Then `|∇f(x)|² ≤ 2C(M − f(x))` for every `x`, and there is a sequence `x_k` with
`∇f(x_k) → 0`. -/
theorem lemma_3_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (hf2 : Differentiable ℝ (fderiv ℝ f)) (hbdd : BddAbove (Set.range f)) (C : ℝ)
    (hC : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) :
    (∀ x, ‖gradient f x‖ ^ 2 ≤ 2 * C * ((⨆ z, f z) - f x)) ∧
      ∃ xs : ℕ → EuclideanSpace ℝ (Fin n), Tendsto (fun k => gradient f (xs k)) atTop (𝓝 0) := by sorry

end GivenDegreeSeq.MeanPolytope
