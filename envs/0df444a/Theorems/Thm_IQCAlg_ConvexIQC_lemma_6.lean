-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_lemma_6
-- name    : IQCAlg.ConvexIQC.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:38.72813+00:00
-- url     : https://prove2.me/theorems/5e0f9cfb-7c83-42c6-8734-24950983f252
-- title:
--   Lemma 6 (sector IQC), p. 13 — (3.14) for gradients of f_k ∈ S(m, L) with a common reference point
-- statement:
--   Let $f_0,f_1,\dots$ be functions in $S(m,L)$ (the same $0<m<L$ for all $k$), and let $(y_\star,u_\star)$ be a common reference point for their gradients: $u_\star=\nabla f_k(y_\star)$ for all $k\ge0$. Let $\phi:=(\nabla f_0,\nabla f_1,\dots)$, so that $u=\phi(y)$ means $u_k=\nabla f_k(y_k)$. Then for every sequence $y=(y_k)_{k\ge0}$ in $\mathbb R^d$ and every $k\ge0$,
--   $$\begin{bmatrix}y_k-y_\star\\ u_k-u_\star\end{bmatrix}^{\mathsf T}\begin{bmatrix}-2mL\,I_d&(L+m)I_d\\(L+m)I_d&-2I_d\end{bmatrix}\begin{bmatrix}y_k-y_\star\\ u_k-u_\star\end{bmatrix}\ \ge\ 0. \tag{3.14}$$
--
--   This is the quadratic inequality of the pointwise (sector) IQC; it is the simplest of the paper's IQCs for gradients.
--
--   **Formalization Note** The block form is written expanded: $-2mL\|y_k-y_\star\|^2+2(L+m)(y_k-y_\star)^{\mathsf T}(u_k-u_\star)-2\|u_k-u_\star\|^2\ge0$, with $u_k=\nabla f_k(y_k)$. The page writes "for all $y\in\ell_2^d$"; the statement holds for every sequence, and that is what is stated.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 13, Lemma 6, (3.14)

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- Lemma 6 (sector IQC), p. 13: the quadratic inequality (3.14), block form expanded. -/
theorem lemma_6 {d : ℕ} (f : ℕ → E d → ℝ) (m L : ℝ) (hf : ∀ k, InSmL (f k) m L)
    (ys us : E d) (hus : ∀ k, gradient (f k) ys = us) :
    ∀ (y : ℕ → E d) (k : ℕ),
      0 ≤ -2 * m * L * ‖y k - ys‖ ^ 2
        + 2 * (L + m) * ⟪y k - ys, gradient (f k) (y k) - us⟫_ℝ
        - 2 * ‖gradient (f k) (y k) - us‖ ^ 2 := by sorry

end IQCAlg.ConvexIQC
