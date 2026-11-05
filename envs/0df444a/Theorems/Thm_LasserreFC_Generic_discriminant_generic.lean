-- Prove2me | Theorems.Thm_LasserreFC_Generic_discriminant_generic
-- name    : LasserreFC.Generic.discriminant_generic
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T12:36:58.732594+00:00
-- url     : https://prove2.me/theorems/fa10a1ea-2593-43bb-ab9d-e701bfb298a8
-- title:
--   §2.4, p. 5 / Appendix A, p. 18 — the discriminant Δ(p₁, …, p_m) does not vanish identically
-- statement:
--   Let $m\le n$ and let $D_1,\dots,D_m$ be positive integers. With the homogenization $\tilde p(\tilde x)=x_0^{D}p(x/x_0)$ at the nominal degree and gradients $\nabla\tilde p$ in all of $\tilde x=(x_0,\dots,x_n)$, there exist $p_i\in\mathbb R[x]_{D_i}$ ($i=1,\dots,m$) such that there is **no** $0\ne\tilde x\in\mathbb C^{n+1}$ with
--
--   $$
--   \tilde p_1(\tilde x)=\cdots=\tilde p_m(\tilde x)=0,\qquad \operatorname{rank}\big[\nabla\tilde p_1(\tilde x)\ \cdots\ \nabla\tilde p_m(\tilde x)\big]<m .
--   $$
--
--   Equivalently (by property (2.1) of §2.4), the discriminant $\Delta(p_1,\dots,p_m)$ does not vanish identically on $\mathbb R[x]_{D_1}\times\cdots\times\mathbb R[x]_{D_m}$: a generic complete intersection is smooth. The paper uses this genericity of $\Delta$ both in Condition 4.3(b) (whose polynomials must not vanish identically for Theorem 1.2) and in Appendix A (p. 18, “when $p_1,\dots,p_k$ are generic, we have $\Delta(p^h_1,\dots,p^h_k)\ne0$”).
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, §2.4, p. 5 (discriminant of several polynomials, after J. Nie, Discriminants and nonnegative polynomials, J. Symbolic Comput. 47 (2012)); genericity used in Condition 4.3(b), p. 14, and Appendix A, p. 18

import Mathlib
import Definitions.Def_LasserreFC_Generic_Homog

namespace LasserreFC.Generic

open MvPolynomial

/-- §2.4, p. 5 (and its use in Appendix A, p. 18): the discriminant `Δ(p₁, …, p_m)` does not
vanish identically. For `m ≤ n` and positive degrees `D₁, …, D_m` there are
`pᵢ ∈ ℝ[x]_{Dᵢ}` for which there is no `0 ≠ x̃ ∈ ℂ^{n+1}` with `p̃₁(x̃) = ⋯ = p̃_m(x̃) = 0` and
`rank [∇p̃₁(x̃) ⋯ ∇p̃_m(x̃)] < m`. -/
theorem discriminant_generic {n m : ℕ} (hm : m ≤ n) (D : Fin m → ℕ) (hD : ∀ i, 0 < D i) :
    ∃ P : Fin m → MvPolynomial (Fin n) ℝ, (∀ i, (P i).totalDegree ≤ D i) ∧
      ¬ ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
          (∀ i, eval xt (homog (D i) (P i)) = 0) ∧
          (Matrix.of fun (k : Fin (n + 1)) (i : Fin m) => hgrad (D i) (P i) xt k).rank < m := by sorry

end LasserreFC.Generic
