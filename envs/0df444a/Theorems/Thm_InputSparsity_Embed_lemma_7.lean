-- Prove2me | Theorems.Thm_InputSparsity_Embed_lemma_7
-- name    : InputSparsity.Embed.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:59.786677+00:00
-- url     : https://prove2.me/theorems/68e5e543-f69a-4f9c-956b-8de942dd8f12
-- title:
--   Lemma 7, p. 10 — fixed-vector preservation under the good bucket events
-- statement:
--   There is an absolute constant $K_y>0$. Fix a bucket map satisfying both $E_h$ and $E_B$. If $y$ is a unit vector in the column space of an orthonormal matrix $U$, $0<\varepsilon\le1$, $0<\delta_y\le1/2$, and $0<W\le K_y\varepsilon^2/\log(1/\delta_y)$, then
--
--   $$\Pr_{\sigma}\!\left(\left|\|\Phi D y\|_2^2-1\right|>\varepsilon\right)\le\delta_y.$$
--
--   This is the fixed-vector guarantee from which the whole-subspace result is obtained.
--
--   **Formalization Note** The constant precedes every problem parameter. The statement uses squared norms, as the proof does; it implies the printed norm form. The $\varepsilon\le1$ restriction keeps both sides meaningful.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 10, Lemma 7

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, Lemma 7, p. 10: a fixed unit vector is preserved with high probability. -/
theorem lemma_7 :
    ∃ Ky : ℝ, 0 < Ky ∧
      ∀ {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ),
        HasOrthonormalCols U →
        ∀ (T W ε δy : ℝ), 0 < T → 0 < W → 0 < ε → ε ≤ 1 →
          0 < δy → δy ≤ 1 / 2 →
          W ≤ Ky * ε ^ 2 / Real.log (1 / δy) →
        ∀ (h : Fin n → Fin t), BucketBound U T W h →
          PerfectOnHeavy U T h →
        ∀ (y : Fin n → ℝ),
          y ∈ LinearMap.range (Matrix.mulVecLin U) → sqNorm y = 1 →
          unifProb (Fin n → Bool)
            {σ | ε < |sqNorm (sketch h σ *ᵥ y) - sqNorm y|} ≤ δy := by sorry

end InputSparsity.Embed
