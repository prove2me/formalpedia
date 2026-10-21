-- Prove2me | Theorems.Thm_NumInvQH_Oblique_A_4_3
-- name    : NumInvQH.Oblique.A_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:43.275392+00:00
-- url     : https://prove2.me/theorems/7ab3c5a5-f10b-44a7-97b9-c955feaf9793
-- title:
--   Theorem A.4(3) — $q(\hat x-x)=q(\hat x)+x^{\mathsf T}Cx$ for $x\in N(A)$, and $q(\hat x)=q((I-JC)A^{+}b)-F^{\mathsf T}JF$
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Let $k,n\in\mathbb N$, $F\in\mathbb R^n$, $C\in\mathbb R^{n\times n}$ symmetric positive semidefinite, $A\in\mathbb R^{k\times n}$ and $b\in R(A)$. Put $q(x)=x^{\mathsf T}Cx-2x^{\mathsf T}F$ and $\mathcal A=\{x\in\mathbb R^n: Ax=b\}$, and let $M=I-A^{+}A$ and $J=(MCM)^{+}$. Assume condition (A.3), $F\in R(A^{\mathsf T})+R(C)$, and let $\hat x=JF+(I-JC)A^{+}b$. Then for every $x\in N(A)$
--
--   $$q(\hat x-x)=q(\hat x)+x^{\mathsf T}Cx,$$
--
--   and, specifically (taking $x=JF$),
--
--   $$q(\hat x)=q\bigl((I-JC)A^{+}b\bigr)-F^{\mathsf T}JF.$$
--
--   The first identity quantifies how far a feasible point is from optimal; the second expresses the optimal value through the particular feasible point $(I-JC)A^{+}b$.
--
--   **Formalization Note** Item (3) refers to the point $\hat x$ of item (2), which the paper defines under condition (A.3); the first identity fails without (A.3), so it is a hypothesis here. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 25–26, Theorem A.4(3)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Theorem A.4(3). `x̂` is the minimizer of item (2), which is defined under condition (A.3);
the first identity is false without (A.3), so (A.3) is a hypothesis. -/
theorem A_4_3 {k n : ℕ}
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
    (∀ x : Fin n → ℝ, A *ᵥ x = 0 →
      quadraticForm C F (xhat - x) = quadraticForm C F xhat + x ⬝ᵥ (C *ᵥ x)) ∧
    quadraticForm C F xhat =
      quadraticForm C F ((1 - J * C) *ᵥ (Ap *ᵥ b)) - F ⬝ᵥ (J *ᵥ F) := by sorry

end NumInvQH.Oblique
