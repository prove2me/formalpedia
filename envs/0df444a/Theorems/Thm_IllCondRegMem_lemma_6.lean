-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_6
-- name    : IllCondRegMem.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:36.152507+00:00
-- url     : https://prove2.me/theorems/604d289d-6929-4948-9bf0-76b324a893dc
-- title:
--   Lemma 6 — spectral dilation: $P_G(P_{F_1}+\rho P_{F_2})P_G=\Sigma_G$ for some $F_1$ of dimension $d/2$
-- statement:
--   Let $d=2q$ be even, $\rho\in(0,1)$, and $G\subseteq\mathbb R^d$ a subspace of dimension at most $d/2$. Let $\Sigma_G$ be a covariance matrix on $G$ (symmetric, with $\Sigma_G=P_G\Sigma_GP_G$) such that
--   $$
--   \rho P_G\preceq\Sigma_G\preceq P_G .
--   $$
--   Then there is a subspace $F_1\subseteq\mathbb R^d$ of dimension $d/2$ such that, with $F_2=F_1^\perp$,
--   $$
--   P_G\big(P_{F_1}+\rho P_{F_2}\big)P_G=\Sigma_G .
--   $$
--   Any covariance on a subspace of at most half the dimension, with spectrum in $[\rho,1]$, is the compression of a matrix with exactly two eigenvalues $1$ and $\rho$ of equal multiplicity. This is how the rotational adversary reproduces, on the explored subspace, the covariance of the masked adversary (Remark 8).
--
--   **Formalization Note** Operators are continuous linear maps on $\mathbb R^d$ and $A\preceq B$ means $\langle x,Ax\rangle\le\langle x,Bx\rangle$ for all $x$.
--
--   Differences from the source:
--   - encoding: ambient dimension d with F₁ of dimension d/2 → d = 2q, finrank G ≤ q, finrank F₁ = q; reason: "dimension d/2" presupposes d even
--   - encoding: matrices, ⪯, covariance matrix → continuous linear maps, quadratic-form inequalities, symmetric operator; reason: Lean representation; same instances
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 6 ([FP57] Theorem 1), p.9 (PDF p.10)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat

open MeasureTheory

namespace IllCondRegMem

/-- **Lemma 6 (Spectral dilation, [FP57] Theorem 1).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 6,
p.9: "Let ρ ∈ (0, 1) and fix a subspace G ⊆ ℝ^d of dimension at most d/2 and a covariance matrix
Σ_G on G, i.e., Σ_G = P_G Σ_G P_G, such that ρP_G ⪯ Σ_G ⪯ P_G. Then, there is some subspace
F₁ ⊆ ℝ^d of dimension d/2 such that letting F₂ = F₁⊥, P_G(P_{F₁} + ρP_{F₂})P_G = Σ_G."

**Formalization Note.** The ambient dimension is `d = 2q` (hypothesis `hd`) ("dimension d/2" presupposes `d`
even). Operators are continuous linear maps on `ℝ^{2q}`; a covariance matrix is a symmetric
operator; `A ⪯ B` is `⟨x, Ax⟩ ≤ ⟨x, Bx⟩` for all `x`; `P_F` is `F.starProjection`. -/
theorem lemma_6 (d q : ℕ) (hd : d = 2 * q) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (G : Submodule ℝ (Vec d))
    (hG : Module.finrank ℝ G ≤ q) (SG : Vec d →L[ℝ] Vec d)
    (hsym : (SG : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (hSG : G.starProjection ∘L SG ∘L G.starProjection = SG)
    (hlow : ∀ x, ρ * inner ℝ x (G.starProjection x) ≤ inner ℝ x (SG x))
    (hup : ∀ x, inner ℝ x (SG x) ≤ inner ℝ x (G.starProjection x)) :
    ∃ F₁ : Submodule ℝ (Vec d), Module.finrank ℝ F₁ = q ∧
      G.starProjection ∘L (F₁.starProjection + ρ • F₁ᗮ.starProjection) ∘L G.starProjection = SG := by sorry

end IllCondRegMem
