-- Prove2me | Theorems.Thm_NumInvQH_Oblique_A_4_4
-- name    : NumInvQH.Oblique.A_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:47.790989+00:00
-- url     : https://prove2.me/theorems/358a995d-56b5-48cc-ab06-5181cb837354
-- title:
--   Theorem A.4(4) — (A.6)–(A.7): $\hat x$ and $q(\hat x)$ through the oblique projector $P_{\bar Y,\bar X}$ onto $\bar Y$ along $N(A)$
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix.
--
--   Let $k,n\in\mathbb N$, $F\in\mathbb R^n$, $C\in\mathbb R^{n\times n}$ symmetric positive semidefinite, $A\in\mathbb R^{k\times n}$ and $b\in R(A)$. Put $q(x)=x^{\mathsf T}Cx-2x^{\mathsf T}F$ and $\mathcal A=\{x\in\mathbb R^n: Ax=b\}$, and let $M=I-A^{+}A$ and $J=(MCM)^{+}$. Assume condition (A.3), $F\in R(A^{\mathsf T})+R(C)$, and let $\hat x=JF+(I-JC)A^{+}b$. Put $\bar X=N(A)$ and
--
--   $$\bar Y=(I-CC^{+})R(A^{\mathsf T})\oplus^\perp C^{+}\bigl(R(A^{\mathsf T})\cap R(C)\bigr).$$
--
--   Then:
--
--   1. the two summands of $\bar Y$ are orthogonal;
--   2. $\bar Y$ and $\bar X$ are complementary subspaces of $\mathbb R^n$, so the oblique projector $P_{\bar Y,\bar X}$ onto $\bar Y$ along $\bar X$ exists;
--   3. writing $P=P_{\bar Y,\bar X}$,
--
--   $$\hat x=(I-P)C^{+}(I-P^{\mathsf T})F+PA^{+}b,\qquad q(\hat x)=q(PA^{+}b)-F^{\mathsf T}(I-P)C^{+}(I-P^{\mathsf T})F;\tag{A.6}$$
--
--   4. (A.7): if $R(A^{\mathsf T})\subseteq R(C)$ then $P_{\bar Y,\bar X}=C^{+}A^{\mathsf T}(AC^{+}A^{\mathsf T})^{+}A$, and if $R(A^{\mathsf T})\cap R(C)=\{0\}$ then $P_{\bar Y,\bar X}=(I-CC^{+})A^{\mathsf T}(A(I-CC^{+})A^{\mathsf T})^{+}A$.
--
--   For a single constraint ($k=1$) the two cases of (A.7) are exhaustive and give items (3) and (4) of Theorem 4.3.
--
--   **Formalization Note** The projector $P_{\bar Y,\bar X}$ is characterised as a matrix $P$ with $P^2=P$, $N(P)=\bar X$, $R(P)=\bar Y$; item 3 is stated for every such $P$ and item 2 guarantees that one exists. The two cases of (A.7) are not exhaustive when $k\ge2$ and each is stated under its own hypothesis, as printed. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 25–26, Theorem A.4(4), eqs. (A.6)–(A.7)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Theorem A.4(4). `Ȳ = Y₁ ⊕⊥ Y₂` with `Y₁ = (I - CC⁻¹) R(Aᵀ)` and `Y₂ = C⁻¹(R(Aᵀ) ∩ R(C))`,
`X̄ = N(A)`. The conclusion has four parts: `Y₁ ⟂ Y₂`; `Ȳ` and `X̄` are complementary, so the
oblique projector `P_{Ȳ,X̄}` onto `Ȳ` along `X̄` exists; (A.6) for every matrix `P` that is that
projector (idempotent, kernel `N(A)`, range `Ȳ`); and (A.7): in each of its two cases the printed
matrix is that projector. -/
theorem A_4_4 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (b : Fin k → ℝ)
    (hb : b ∈ LinearMap.range (Matrix.toLin' A))
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef)
    (F : Fin n → ℝ)
    (hF : F ∈ LinearMap.range (Matrix.toLin' Aᵀ) ⊔ LinearMap.range (Matrix.toLin' C))
    (Ap : Matrix (Fin n) (Fin k) ℝ)
    (hAp : LocalDistanceNetwork.IsMoorePenroseInverse A Ap)
    (Cp : Matrix (Fin n) (Fin n) ℝ)
    (hCp : LocalDistanceNetwork.IsMoorePenroseInverse C Cp)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : LocalDistanceNetwork.IsMoorePenroseInverse ((1 - Ap * A) * C * (1 - Ap * A)) J)
    (P₁p : Matrix (Fin k) (Fin k) ℝ)
    (hP₁p : LocalDistanceNetwork.IsMoorePenroseInverse (A * Cp * Aᵀ) P₁p)
    (P₂p : Matrix (Fin k) (Fin k) ℝ)
    (hP₂p : LocalDistanceNetwork.IsMoorePenroseInverse (A * (1 - C * Cp) * Aᵀ) P₂p) :
    let xhat := J *ᵥ F + (1 - J * C) *ᵥ (Ap *ᵥ b)
    let Xbar := LinearMap.ker (Matrix.toLin' A)
    let Y₁ := Submodule.map (Matrix.toLin' (1 - C * Cp)) (LinearMap.range (Matrix.toLin' Aᵀ))
    let Y₂ := Submodule.map (Matrix.toLin' Cp)
      (LinearMap.range (Matrix.toLin' Aᵀ) ⊓ LinearMap.range (Matrix.toLin' C))
    let Ybar := Y₁ ⊔ Y₂
    let IsObliqueProj : Matrix (Fin n) (Fin n) ℝ → Prop := fun P =>
      P * P = P ∧ LinearMap.ker (Matrix.toLin' P) = Xbar ∧ LinearMap.range (Matrix.toLin' P) = Ybar
    (∀ x ∈ Y₁, ∀ y ∈ Y₂, x ⬝ᵥ y = 0) ∧
    IsCompl Ybar Xbar ∧
    (∀ P : Matrix (Fin n) (Fin n) ℝ, IsObliqueProj P →
      xhat = (1 - P) *ᵥ (Cp *ᵥ ((1 - Pᵀ) *ᵥ F)) + P *ᵥ (Ap *ᵥ b) ∧
      quadraticForm C F xhat =
        quadraticForm C F (P *ᵥ (Ap *ᵥ b)) - F ⬝ᵥ ((1 - P) *ᵥ (Cp *ᵥ ((1 - Pᵀ) *ᵥ F)))) ∧
    (LinearMap.range (Matrix.toLin' Aᵀ) ≤ LinearMap.range (Matrix.toLin' C) →
      IsObliqueProj (Cp * Aᵀ * P₁p * A)) ∧
    (Disjoint (LinearMap.range (Matrix.toLin' Aᵀ)) (LinearMap.range (Matrix.toLin' C)) →
      IsObliqueProj ((1 - C * Cp) * Aᵀ * P₂p * A)) := by sorry

end NumInvQH.Oblique
