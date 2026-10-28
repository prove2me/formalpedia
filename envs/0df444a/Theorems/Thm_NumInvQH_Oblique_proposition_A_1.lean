-- Prove2me | Theorems.Thm_NumInvQH_Oblique_proposition_A_1
-- name    : NumInvQH.Oblique.proposition_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:38.711357+00:00
-- url     : https://prove2.me/theorems/00c5b28a-1a52-4bec-b540-b7983bfdb88b
-- title:
--   Proposition A.1 — properties of the Moore–Penrose pseudoinverse (real case)
-- statement:
--   Throughout, $X^{+}$ denotes the Moore–Penrose pseudoinverse of a real matrix $X$: the unique matrix satisfying $XX^{+}X=X$, $X^{+}XX^{+}=X^{+}$, $(XX^{+})^{\mathsf T}=XX^{+}$, $(X^{+}X)^{\mathsf T}=X^{+}X$ (the paper writes $X^{-1}$). $R(\cdot)$ is the column space and $N(\cdot)$ the null space of a matrix. For real matrices of compatible sizes the following hold.
--
--   1. $(A^{\mathsf T})^{+}=(A^{+})^{\mathsf T}$.
--   2. $R(A^{+})=R(A^{\mathsf T})$.
--   3. If $U$ is an orthogonal projector ($U^2=U$, $U^{\mathsf T}=U$), then $U(VU)^{+}=(VU)^{+}$.
--   4. If $V$ is an orthogonal projector, then $(VU)^{+}V=(VU)^{+}$.
--   5. $A^{+}=A^{\mathsf T}(AA^{\mathsf T})^{+}=(A^{\mathsf T}A)^{+}A^{\mathsf T}$.
--
--   In display form, item 5 reads
--
--   $$A^{+}=A^{\mathsf T}(AA^{\mathsf T})^{+}=(A^{\mathsf T}A)^{+}A^{\mathsf T}.$$
--
--   These rules are used throughout Appendix A, in particular to identify the projector $JC$ in the proof of Theorem A.4.
--
--   **Formalization Note** The paper states the proposition over $\mathbb C$ with the conjugate transpose; this is its real specialisation, which is all that Theorem A.4 and Theorem 4.3 use. Every pseudoinverse is an explicit matrix argument together with the hypothesis that it satisfies the four Penrose equations (`LocalDistanceNetwork.IsMoorePenroseInverse`); since such a matrix exists and is unique, this is the same as using "the" pseudoinverse. Lean's matrix inverse `⁻¹` is never used for a matrix; it appears only for real scalars. Each item is a separate conjunct, universally quantified over the matrix sizes.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 24, Proposition A.1

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- Proposition A.1, specialised from complex to real matrices (conjugate transpose = transpose).
Every pseudoinverse is a matrix carrying the four Penrose equations (A.2). -/
theorem proposition_A_1 :
    -- (1) the pseudoinverse of the transpose is the transpose of the pseudoinverse
    (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin m) ℝ)
        (Y : Matrix (Fin m) (Fin n) ℝ),
        LocalDistanceNetwork.IsMoorePenroseInverse A X →
        LocalDistanceNetwork.IsMoorePenroseInverse Aᵀ Y → Y = Xᵀ) ∧
    -- (2) the column space of the pseudoinverse is the column space of the transpose
    (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin m) ℝ),
        LocalDistanceNetwork.IsMoorePenroseInverse A X →
        LinearMap.range (Matrix.toLin' X) = LinearMap.range (Matrix.toLin' Aᵀ)) ∧
    -- (3) a left orthogonal-projector factor can be dropped
    (∀ {n p : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin p) (Fin n) ℝ)
        (X : Matrix (Fin n) (Fin p) ℝ),
        U * U = U → Uᵀ = U →
        LocalDistanceNetwork.IsMoorePenroseInverse (V * U) X → U * X = X) ∧
    -- (4) a right orthogonal-projector factor can be dropped
    (∀ {n p : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin p) ℝ)
        (X : Matrix (Fin p) (Fin n) ℝ),
        V * V = V → Vᵀ = V →
        LocalDistanceNetwork.IsMoorePenroseInverse (V * U) X → X * V = X) ∧
    -- (5) the pseudoinverse through the two Gram matrices
    (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin m) ℝ)
        (Y : Matrix (Fin m) (Fin m) ℝ) (Z : Matrix (Fin n) (Fin n) ℝ),
        LocalDistanceNetwork.IsMoorePenroseInverse A X →
        LocalDistanceNetwork.IsMoorePenroseInverse (A * Aᵀ) Y →
        LocalDistanceNetwork.IsMoorePenroseInverse (Aᵀ * A) Z →
        X = Aᵀ * Y ∧ X = Z * Aᵀ) := by sorry

end NumInvQH.Oblique
