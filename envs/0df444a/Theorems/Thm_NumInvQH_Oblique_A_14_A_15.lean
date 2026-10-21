-- Prove2me | Theorems.Thm_NumInvQH_Oblique_A_14_A_15
-- name    : NumInvQH.Oblique.A_14_A_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:29.626993+00:00
-- url     : https://prove2.me/theorems/e67b8518-b551-4628-8184-8c935dbc7058
-- title:
--   Eqs. (A.14)–(A.15) — $(I-CJ)(R(A^{\mathsf T})+R(C))\subseteq R(A^{\mathsf T})$, proof of Theorem A.4(1)
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Let $C\in\mathbb R^{n\times n}$ be symmetric positive semidefinite, $A\in\mathbb R^{k\times n}$, $M=I-A^{+}A$ and $J=(MCM)^{+}$. Then
--
--   $$(I-CJ)\bigl(R(A^{\mathsf T})+R(C)\bigr)\subseteq R(A^{\mathsf T}).\tag{A.14}$$
--
--   Consequently, for every $F\in\mathbb R^n$ satisfying condition (A.3), $F\in R(A^{\mathsf T})+R(C)$,
--
--   $$(I-CJ)F\in R(A^{\mathsf T}).\tag{A.15}$$
--
--   This is the step that makes the linear term $x^{\mathsf T}(I-CJ)F$ constant on the affine set $\{Ax=b\}$, which leads to the completed square (A.16).
--
--   **Formalization Note** (A.14) is stated as an inclusion of subspaces: the image of $R(A^{\mathsf T})+R(C)$ under the linear map $x\mapsto(I-CJ)x$ is contained in $R(A^{\mathsf T})$. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 27, eqs. (A.14)–(A.15), proof of Theorem A.4(1)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Equations (A.14) and (A.15) in the proof of Theorem A.4(1): the image of
`R(Aᵀ) + R(C)` under `I - CJ` lies in `R(Aᵀ)`, and hence `(I - CJ)F ∈ R(Aᵀ)` under (A.3). -/
theorem A_14_A_15 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) (Ap : Matrix (Fin n) (Fin k) ℝ)
    (hAp : LocalDistanceNetwork.IsMoorePenroseInverse A Ap)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : LocalDistanceNetwork.IsMoorePenroseInverse ((1 - Ap * A) * C * (1 - Ap * A)) J)
    (F : Fin n → ℝ)
    (hF : F ∈ LinearMap.range (Matrix.toLin' Aᵀ) ⊔ LinearMap.range (Matrix.toLin' C)) :
    Submodule.map (Matrix.toLin' (1 - C * J))
        (LinearMap.range (Matrix.toLin' Aᵀ) ⊔ LinearMap.range (Matrix.toLin' C)) ≤
      LinearMap.range (Matrix.toLin' Aᵀ) ∧
    (1 - C * J) *ᵥ F ∈ LinearMap.range (Matrix.toLin' Aᵀ) := by sorry

end NumInvQH.Oblique
