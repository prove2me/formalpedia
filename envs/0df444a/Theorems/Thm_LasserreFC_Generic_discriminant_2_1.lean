-- Prove2me | Theorems.Thm_LasserreFC_Generic_discriminant_2_1
-- name    : LasserreFC.Generic.discriminant_2_1
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T12:37:06.245738+00:00
-- url     : https://prove2.me/theorems/3a7ee723-e030-49ff-a372-9f07beb8fd20
-- title:
--   §2.4, p. 5, (2.1) — the discriminant Δ(p₁, …, p_m) of several polynomials vanishes iff the homogenized system is singular
-- statement:
--   Let $m\le n$ and let $D_1,\dots,D_m$ be nonnegative integers (nominal degrees). For $p\in\mathbb R[x]$, $x=(x_1,\dots,x_n)$, with $\deg p\le D$, write $\tilde p(\tilde x)=x_0^{D}\,p(x/x_0)$ for its homogenization at degree $D$, a form in $\tilde x=(x_0,x_1,\dots,x_n)$, and $\nabla\tilde p$ for its gradient in all $n+1$ variables $\tilde x$.
--
--   There is a real polynomial $\Delta$ in the coefficients of $(p_1,\dots,p_m)\in\mathbb R[x]_{D_1}\times\cdots\times\mathbb R[x]_{D_m}$ (the discriminant of several polynomials) such that for every such tuple
--
--   $$
--   \Delta(p_1,\dots,p_m)=0\iff \exists\,0\ne\tilde x\in\mathbb C^{n+1}:\quad \tilde p_1(\tilde x)=\cdots=\tilde p_m(\tilde x)=0,\quad \operatorname{rank}\big[\nabla\tilde p_1(\tilde x)\ \cdots\ \nabla\tilde p_m(\tilde x)\big]<m .
--   $$
--
--   This is property (2.1) of §2.4, applied to the homogenized polynomials, as it is used in Condition 4.3(b): when $\Delta(h_1,\dots,h_{m_1},g_{j_1},\dots,g_{j_r})\ne0$, the projective variety cut out by these polynomials is smooth, so the gradients of the active constraints are linearly independent at every common zero.
--
--   **Formalization Note** The polynomial $\Delta$ is a polynomial in the coefficient variables $(i,\alpha)$ (the coefficient of $x^\alpha$ in $p_i$); only its values on tuples respecting the degree bounds matter. The paper states (2.1) for forms with some $d_i>1$ (citing Nie, *Discriminants and nonnegative polynomials*); for a real-valued characterization the existence of such a polynomial follows for all nominal degrees from the elimination theorem (Theorem 2.5, p. 6), taking a sum of squares of the eliminating polynomials, so no degree restriction is imposed.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, §2.4, p. 5, property (2.1) (discriminants of several polynomials, after J. Nie, Discriminants and nonnegative polynomials, J. Symbolic Comput. 47 (2012) 167–191); used in Condition 4.3(b), p. 14

import Mathlib
import Definitions.Def_LasserreFC_Generic_Homog

namespace LasserreFC.Generic

open MvPolynomial

/-- §2.4, p. 5, property (2.1): the discriminant of several polynomials. For `m ≤ n` and
nominal degrees `D₁, …, D_m` there is a real polynomial `Δ` in the coefficients of
`(p₁, …, p_m) ∈ ℝ[x]_{D₁} × ⋯ × ℝ[x]_{D_m}` such that, for every such tuple,
`Δ(p₁, …, p_m) = 0` iff there is `0 ≠ x̃ ∈ ℂ^{n+1}` with `p̃₁(x̃) = ⋯ = p̃_m(x̃) = 0` and
`rank [∇p̃₁(x̃) ⋯ ∇p̃_m(x̃)] < m` (gradients in all of `x̃ = (x₀, x₁, …, xₙ)`). -/
theorem discriminant_2_1 {n m : ℕ} (hm : m ≤ n) (D : Fin m → ℕ) :
    ∃ Δ : MvPolynomial (Fin m × (Fin n →₀ ℕ)) ℝ,
      ∀ P : Fin m → MvPolynomial (Fin n) ℝ, (∀ i, (P i).totalDegree ≤ D i) →
        (MvPolynomial.eval (tupleCoeffs P) Δ = 0 ↔
          ∃ xt : Fin (n + 1) → ℂ, xt ≠ 0 ∧
            (∀ i, eval xt (homog (D i) (P i)) = 0) ∧
            (Matrix.of fun (k : Fin (n + 1)) (i : Fin m) => hgrad (D i) (P i) xt k).rank < m) := by sorry

end LasserreFC.Generic
