-- Prove2me | Theorems.Thm_NumInvQH_Oblique_A_16
-- name    : NumInvQH.Oblique.A_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:37.044363+00:00
-- url     : https://prove2.me/theorems/c46dd9eb-5fc4-44c1-b85d-fea6530d54dc
-- title:
--   Eq. (A.16) — completion of squares $q(x)=\|C^{1/2}(x-JF)\|^2-F^{\mathsf T}JF-2(A^{+}b)^{\mathsf T}(I-CJ)F$ on $\{Ax=b\}$
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Let $k,n\in\mathbb N$, $F\in\mathbb R^n$, $C\in\mathbb R^{n\times n}$ symmetric positive semidefinite, $A\in\mathbb R^{k\times n}$ and $b\in R(A)$. Put $q(x)=x^{\mathsf T}Cx-2x^{\mathsf T}F$ and $\mathcal A=\{x\in\mathbb R^n: Ax=b\}$, and let $M=I-A^{+}A$ and $J=(MCM)^{+}$. Assume condition (A.3), $F\in R(A^{\mathsf T})+R(C)$. Then for every $x$ with $Ax=b$,
--
--   $$q(x)=x^{\mathsf T}Cx-2x^{\mathsf T}CJF-2x^{\mathsf T}(I-CJ)F=\|C^{1/2}(x-JF)\|^2-F^{\mathsf T}JF-2(A^{+}b)^{\mathsf T}(I-CJ)F.$$
--
--   On the affine set the objective is therefore a squared seminorm of $x-JF$ plus a constant; this gives the bound from below in Theorem A.4(1) and reduces Theorem A.4(2) to Proposition A.3.
--
--   **Formalization Note** $\|C^{1/2}y\|^2$ is written $y^{\mathsf T}Cy$, which equals it for the positive semidefinite square root. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 27, eq. (A.16), proof of Theorem A.4(1)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Equation (A.16) in the proof of Theorem A.4(1): completion of squares on the affine set
`Ax = b` under condition (A.3). `‖C^{1/2} y‖²` is written `y ⬝ᵥ (C *ᵥ y)`. -/
theorem A_16 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ)
    (hb : b ∈ LinearMap.range (Matrix.toLin' A))
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef)
    (F : Fin n → ℝ)
    (hF : F ∈ LinearMap.range (Matrix.toLin' Aᵀ) ⊔ LinearMap.range (Matrix.toLin' C))
    (Ap : Matrix (Fin n) (Fin k) ℝ)
    (hAp : LocalDistanceNetwork.IsMoorePenroseInverse A Ap)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : LocalDistanceNetwork.IsMoorePenroseInverse ((1 - Ap * A) * C * (1 - Ap * A)) J) :
    ∀ x : Fin n → ℝ, A *ᵥ x = b →
      quadraticForm C F x =
          x ⬝ᵥ (C *ᵥ x) - 2 * (x ⬝ᵥ (C *ᵥ (J *ᵥ F))) - 2 * (x ⬝ᵥ ((1 - C * J) *ᵥ F)) ∧
      quadraticForm C F x =
          (x - J *ᵥ F) ⬝ᵥ (C *ᵥ (x - J *ᵥ F)) - F ⬝ᵥ (J *ᵥ F)
            - 2 * ((Ap *ᵥ b) ⬝ᵥ ((1 - C * J) *ᵥ F)) := by sorry

end NumInvQH.Oblique
