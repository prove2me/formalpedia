-- Prove2me | Theorems.Thm_MatrixSpencer_lemma_2_6
-- name    : MatrixSpencer.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:14.797305+00:00
-- url     : https://prove2.me/theorems/7b018422-074e-462e-8c73-19ff75cbe2c6
-- title:
--   Lemma 2.6, p.8 — inverse second moment bounds
-- statement:
--   Assume (2.2), and let $M_1,\dots,M_n\in\mathbb R^{d\times d}$ be symmetric with $\sum_iM_i^2\preceq\eta I$. Let $B=\sum_ig_iM_i$, $R=(I-B)^{-1}$ and $d\mu\propto e^{-V(B)}d\gamma_n$. Then
--
--   $$\mathbb E_\mu(R\otimes R)\preceq2I,\qquad\mathbb E_\mu\mathrm{Tr}\,R^2\le2d.$$
--
--   This dimension-free control of the inverse moments of a log-barrier tilt is the paper's key technical lemma: it bounds $F'$ along the interpolation.
--
--   **Formalization Note** The first bound is stated in quadratic form, for every vector $z$ indexed by pairs: $\int w\,z^\top(R\otimes R)z\,d\gamma_n\le2\|z\|^2\int w\,d\gamma_n$. As $R\otimes R$ is symmetric, these forms determine $\preceq$.
--
--   Differences from the source:
--   - reading: M₁,…,Mₙ ∈ ℝ^{d×d} (no word "symmetric") → the Mᵢ are symmetric; reason: ⪯ and V(X) = Tr v(X) are defined for symmetric matrices only (p.6, p.8), and the only use of the statement has symmetric Mᵢ
--   - encoding: V = +∞ outside the unit ball → the real weight e^{−V} is 0 there; reason: the value +∞ is never computed with
--   - encoding: E_µ(R ⊗ R) ⪯ 2I, a matrix integral under a normalized measure → for every z, ∫ w zᵀ(R⊗R)z dγₙ ≤ 2‖z‖²∫ w dγₙ, with ∫ w > 0 and integrability in the conclusion; reason: R ⊗ R is symmetric, so quadratic forms determine ⪯, and ∫ w > 0 makes the two normalizations equal
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.6, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MatrixSpencer_Param22
import Definitions.Def_MatrixSpencer_gam
import Definitions.Def_MatrixSpencer_series
import Definitions.Def_MatrixSpencer_weight
import Definitions.Def_MatrixSpencer_resolvent
open Matrix
open scoped Kronecker

namespace MatrixSpencer

/-- **Lemma 2.6 (Inverse second moment bounds).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.6, p.8 (PDF p.10): "Assume that (2.2) holds. Let M₁, …, Mₙ ∈ ℝ^{d×d} satisfy ∑ⁿᵢ₌₁ Mᵢ² ⪯ ηI. Let
B = ∑ⁿᵢ₌₁ gᵢMᵢ, and let R = (I − B)⁻¹. Then, E_µ(R ⊗ R) ⪯ 2I, E_µ Tr R² ≤ 2d, (2.4) where dµ ∝ e^{−V(B)}dγₙ."

**Formalization Note.** The `Mᵢ` are symmetric, as in `theorem_2_5`. `E_µ T = (∫ T e^{−V(B)} dγₙ)/Z` with
`Z = ∫ e^{−V(B)} dγₙ`, and `Z > 0` is part of the conclusion, so the inequalities are stated after
multiplying by `Z`. `E_µ(R ⊗ R) ⪯ 2I` is stated in quadratic form, for every vector `z` indexed by
`Fin d × Fin d`, with the integrand integrable: `R ⊗ R` is symmetric, so these forms determine `⪯`. -/
theorem lemma_2_6 {n d : ℕ} (α β : ℝ) (p : ℕ) (η : ℝ) (h : Param22 α β p η)
    (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i, (M i).IsSymm)
    (hV : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - ∑ i, M i ^ 2).PosSemidef) :
    0 < ∫ g, weight α β p (series M g) ∂(gam n) ∧
    (∀ z : Fin d × Fin d → ℝ,
      MeasureTheory.Integrable (fun g => weight α β p (series M g) *
        (z ⬝ᵥ (resolvent (series M g) ⊗ₖ resolvent (series M g)) *ᵥ z)) (gam n) ∧
      ∫ g, weight α β p (series M g) *
          (z ⬝ᵥ (resolvent (series M g) ⊗ₖ resolvent (series M g)) *ᵥ z) ∂(gam n) ≤
        2 * (z ⬝ᵥ z) * ∫ g, weight α β p (series M g) ∂(gam n)) ∧
    MeasureTheory.Integrable (fun g => weight α β p (series M g) *
      (resolvent (series M g) ^ 2).trace) (gam n) ∧
    ∫ g, weight α β p (series M g) * (resolvent (series M g) ^ 2).trace ∂(gam n) ≤
      2 * d * ∫ g, weight α β p (series M g) ∂(gam n) := by sorry

end MatrixSpencer
