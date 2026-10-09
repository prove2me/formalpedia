-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_eq_3_16
-- name    : IQCAlg.ConvexIQC.eq_3_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:36.71618+00:00
-- url     : https://prove2.me/theorems/13a66e1c-d5cb-4906-ac59-de107bf22441
-- title:
--   (3.16), proof of Lemma 8, p. 14 — q_k = (L − m)g(y_k) − ½‖∇g(y_k)‖² ≥ 0 when ∇f(y⋆) = 0
-- statement:
--   Let $f\in S(m,L)$ and let $y_\star$ be a point with $\nabla f(y_\star)=0$. Define
--   $$g(x):=f(x)-f(y_\star)-\frac m2\|x-y_\star\|^2,\qquad \nabla g(x)=\nabla f(x)-m(x-y_\star).$$
--   Then for every sequence $y=(y_k)_{k\ge0}$ in $\mathbb R^d$ and every $k\ge0$,
--   $$q_k:=(L-m)\,g(y_k)-\frac12\|\nabla g(y_k)\|^2\ \ge\ 0. \tag{3.16}$$
--
--   The quantities $q_k$ are the lower bounds into which the terms of the off-by-one and weighted off-by-one IQCs telescope.
--
--   **Formalization Note** The page's proof of Lemma 8 uses $g(x)\ge g(y_\star)=0$ and $\nabla g(y_\star)=0$, which hold only when $u_\star=\nabla f(y_\star)=0$; for $u_\star\ne0$ this inequality is false (at $y_k=y_\star$, $q_k=-\|u_\star\|^2/2$). The hypothesis $\nabla f(y_\star)=0$ is therefore added (it is Lemma 9's hypothesis). Lemmas 8 and 10 themselves are stated for every reference.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 14, proof of Lemma 8, (3.16)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- (3.16), proof of Lemma 8, p. 14: `q_k ≥ 0`, for a reference with `∇f(y⋆) = 0`. -/
theorem eq_3_16 {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) (ys : E d)
    (h0 : gradient f ys = 0) :
    ∀ (y : ℕ → E d) (k : ℕ), 0 ≤ qTerm f ys m L (y k) := by sorry

end IQCAlg.ConvexIQC
