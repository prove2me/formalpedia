-- Prove2me | Theorems.Thm_MatrixSpencer_lemma_C_2
-- name    : MatrixSpencer.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:02.841418+00:00
-- url     : https://prove2.me/theorems/cf7e34d2-1974-4f72-a677-36550b8a7ed2
-- title:
--   Lemma C.2, p.27 — block Cauchy–Schwarz inequalities (C.4), (C.5)
-- statement:
--   Let $C_1,\dots,C_n,D_1,\dots,D_n\in\mathbb R^{d\times d}$ be symmetric matrices and $z_1,\dots,z_n\in\mathbb R^d\otimes\mathbb R^r$. Then
--
--   $$\Bigl|\sum_{i,j=1}^n\langle z_i,(C_jC_i\otimes I)z_j\rangle\Bigr|\le\sum_{i,j=1}^n\mathrm{Tr}(C_iC_j)\langle z_i,z_j\rangle$$
--
--   and
--
--   $$\Bigl|\sum_{i,j=1}^n\langle z_i,(C_jD_i\otimes I)z_j\rangle\Bigr|\le\Bigl(\sum_{i,j=1}^n\mathrm{Tr}(C_iC_j)\langle z_i,z_j\rangle\Bigr)^{1/2}\Bigl(\sum_{i,j=1}^n\mathrm{Tr}(D_iD_j)\langle z_i,z_j\rangle\Bigr)^{1/2}.$$
--
--   These estimate the terms $E_jE_i\otimes I$ in the curvature identity.
--
--   Differences from the source:
--   - encoding: ℝ^{d×d}) (a misprinted parenthesis) and ℝᵈ ⊗ ℝʳ → Matrix (Fin d) (Fin d) ℝ and Fin d × Fin r → ℝ; reason: the evident meaning; ⊗ is the Kronecker product
--   - encoding: (·)^{1/2} of the double sums → √ of the double sums; reason: the sums are nonnegative, as squared Euclidean norms
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma C.2, p.27 (PDF p.29)

import Mathlib
open Matrix
open scoped Kronecker

namespace MatrixSpencer

/-- **Lemma C.2.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma C.2, p.27 (PDF p.29): "Let C₁, …, Cₙ, D₁, …, Dₙ ∈ ℝ^{d×d}) be symmetric matrices and let z₁, …, zₙ ∈
ℝᵈ ⊗ ℝʳ. Then, we have that |Σⁿᵢ,ⱼ₌₁ ⟨zᵢ, (CⱼCᵢ ⊗ I)zⱼ⟩| ≤ Σⁿᵢ,ⱼ₌₁ Tr(CᵢCⱼ) ⟨zᵢ, zⱼ⟩, (C.4) and
|Σⁿᵢ,ⱼ₌₁ ⟨zᵢ, (CⱼDᵢ ⊗ I)zⱼ⟩| ≤ (Σⁿᵢ,ⱼ₌₁ Tr(CᵢCⱼ) ⟨zᵢ, zⱼ⟩)^{1/2} (Σⁿᵢ,ⱼ₌₁ Tr(DᵢDⱼ) ⟨zᵢ, zⱼ⟩)^{1/2}. (C.5)"

**Formalization Note.** `ℝᵈ ⊗ ℝʳ` is `Fin d × Fin r → ℝ` and `⊗` the Kronecker product. The two double sums
under the square roots in (C.5) are nonnegative (each is a squared Euclidean norm, as the page's proof
shows), so `√` is the page's `^{1/2}`. -/
theorem lemma_C_2 {n d r : ℕ} (C D : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ i, (C i).IsSymm) (hD : ∀ i, (D i).IsSymm) (z : Fin n → (Fin d × Fin r → ℝ)) :
    |∑ i, ∑ j, z i ⬝ᵥ ((C j * C i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ z j| ≤
      ∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j) ∧
    |∑ i, ∑ j, z i ⬝ᵥ ((C j * D i) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ)) *ᵥ z j| ≤
      √(∑ i, ∑ j, (C i * C j).trace * (z i ⬝ᵥ z j)) *
        √(∑ i, ∑ j, (D i * D j).trace * (z i ⬝ᵥ z j)) := by sorry

end MatrixSpencer
