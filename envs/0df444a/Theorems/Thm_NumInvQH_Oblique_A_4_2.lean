-- Prove2me | Theorems.Thm_NumInvQH_Oblique_A_4_2
-- name    : NumInvQH.Oblique.A_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:36.042987+00:00
-- url     : https://prove2.me/theorems/28bead71-4c16-4f3c-95da-b6c182bb2395
-- title:
--   Theorem A.4(2) — the minimizers of $q$ on $\{Ax=b\}$ are $\hat x+N(C)\cap N(A)$, $\hat x=JF+(I-JC)A^{+}b$ of minimum norm
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Let $k,n\in\mathbb N$, $F\in\mathbb R^n$, $C\in\mathbb R^{n\times n}$ symmetric positive semidefinite, $A\in\mathbb R^{k\times n}$ and $b\in R(A)$. Put $q(x)=x^{\mathsf T}Cx-2x^{\mathsf T}F$ and $\mathcal A=\{x\in\mathbb R^n: Ax=b\}$, and let $M=I-A^{+}A$ and $J=(MCM)^{+}$. Assume condition (A.3), $F\in R(A^{\mathsf T})+R(C)$, and put
--
--   $$\hat x=JF+(I-JC)A^{+}b.\tag{A.5}$$
--
--   Then the minimal value of $q$ on $\mathcal A$ is attained, and the set of all minimizers of $q$ on $\mathcal A$ is exactly
--
--   $$\Xi=\hat x+N(C)\cap N(A).\tag{A.4}$$
--
--   Furthermore, $\hat x$ has the smallest Euclidean norm among all minimizers.
--
--   With $A=S_-^{\mathsf T}$, $C=\tilde c^{S\star}$ this yields the formulas (4.12)–(4.13) of Theorem 4.3.
--
--   **Formalization Note** The conclusion is a set equality between the argmin set of `Basic` and the explicit affine set, together with the minimum-norm property over that set. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 25–26, Theorem A.4(2), eqs. (A.4)–(A.5)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Theorem A.4(2): the complete argmin set and its minimum-norm member. -/
theorem A_4_2 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ)
    (hb : b ∈ LinearMap.range (Matrix.toLin' A))
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef)
    (F : Fin n → ℝ)
    (hF : F ∈ LinearMap.range (Matrix.toLin' Aᵀ) ⊔ LinearMap.range (Matrix.toLin' C))
    (Ap : Matrix (Fin n) (Fin k) ℝ)
    (hAp : LocalDistanceNetwork.IsMoorePenroseInverse A Ap)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : LocalDistanceNetwork.IsMoorePenroseInverse ((1 - Ap * A) * C * (1 - Ap * A)) J) :
    let xhat := J *ᵥ F + (1 - J * C) *ᵥ (Ap *ᵥ b)
    let Ξ := affineArgmin A b (quadraticForm C F)
    Ξ = {x | ∃ z : Fin n → ℝ, C *ᵥ z = 0 ∧ A *ᵥ z = 0 ∧ x = xhat + z} ∧
      IsMinNorm Ξ xhat := by sorry

end NumInvQH.Oblique
