-- Prove2me | Theorems.Thm_NumInvQH_Oblique_proposition_A_3
-- name    : NumInvQH.Oblique.proposition_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:33.787871+00:00
-- url     : https://prove2.me/theorems/3187ab00-cb18-4658-8cfe-194e5ae8dcce
-- title:
--   Proposition A.3 — affinely constrained least squares: argmin $=\xi+N(A_1)\cap N(A_2)$, $\xi$ of minimum norm (real case)
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Let $A_1\in\mathbb R^{m\times n}$, $b_1\in\mathbb R^m$, $A_2\in\mathbb R^{k\times n}$ and $b_2\in R(A_2)$. Put $M=I-A_2^{+}A_2$ and
--
--   $$\xi=(A_1M)^{+}A_1A_1^{+}b_1+\bigl(I-(A_1M)^{+}A_1\bigr)A_2^{+}b_2.$$
--
--   Then the set of all minimizers of $\|A_1x-b_1\|^2$ subject to $A_2x=b_2$ is exactly
--
--   $$\Xi=\xi+N(A_1)\cap N(A_2),$$
--
--   and $\xi$ is the element of $\Xi$ with the smallest Euclidean norm.
--
--   The proposition writes the solution of a constrained least-squares problem with the oblique projector $(A_1M)^{+}A_1$ in plain view; it is the step to which Theorem A.4(2) reduces.
--
--   **Formalization Note** The paper states the proposition over $\mathbb C$ (citing Černý 2009, Corollary 4.3); this is its real specialisation. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars. The argmin is the set of all global minimizers over the whole affine set, stated as a set equality.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 25, Proposition A.3

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Proposition A.3, specialized from complex to real matrices. -/
theorem proposition_A_3 {k m n : ℕ}
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (b₁ : Fin m → ℝ)
    (A₂ : Matrix (Fin k) (Fin n) ℝ) (b₂ : Fin k → ℝ)
    (hb₂ : b₂ ∈ LinearMap.range (Matrix.toLin' A₂))
    (A₁p : Matrix (Fin n) (Fin m) ℝ)
    (hA₁p : LocalDistanceNetwork.IsMoorePenroseInverse A₁ A₁p)
    (A₂p : Matrix (Fin n) (Fin k) ℝ)
    (hA₂p : LocalDistanceNetwork.IsMoorePenroseInverse A₂ A₂p)
    (J : Matrix (Fin n) (Fin m) ℝ)
    (hJ : LocalDistanceNetwork.IsMoorePenroseInverse (A₁ * (1 - A₂p * A₂)) J) :
    let ξ := J *ᵥ (A₁ *ᵥ (A₁p *ᵥ b₁)) + (1 - J * A₁) *ᵥ (A₂p *ᵥ b₂)
    let Ξ := affineArgmin A₂ b₂ (squaredResidual A₁ b₁)
    Ξ = {x | ∃ z : Fin n → ℝ, A₁ *ᵥ z = 0 ∧ A₂ *ᵥ z = 0 ∧ x = ξ + z} ∧
      IsMinNorm Ξ ξ := by sorry

end NumInvQH.Oblique
