-- Prove2me | Theorems.Thm_InputSparsity_Embed_lemma_3
-- name    : InputSparsity.Embed.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:31.501217+00:00
-- url     : https://prove2.me/theorems/66953755-a9d8-4f6a-9a39-e0664dfd986c
-- title:
--   Lemma 3, p. 8 — light-coordinate concentration given the bucket event
-- statement:
--   There is an absolute constant $K_L>0$ with the following property. Let $U$ have orthonormal columns, let $y$ be a unit vector in its column space, and let $h$ satisfy the light-bucket bound $E_h$ with positive parameters $T,W$. For $2\le\ell\le1/W$, writing $y_L$ for the coordinates with leverage at most $T$,
--
--   $$\Pr_{\sigma}\!\left(\left|\|\Phi D y_L\|_2^2-\|y_L\|_2^2\right|>K_L\sqrt{W\ell}\right)\le e^{-\ell}.$$
--
--   This gives fixed-vector control over the light coordinates after the buckets have been chosen.
--
--   **Formalization Note** The probability is over signs only, for each fixed bucket map satisfying $E_h$. The positive $W$ avoids division by zero, and the sorted light range is represented by leverage threshold.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 8, Lemma 3

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, Lemma 3, p. 8: concentration of the light part for fixed buckets. -/
theorem lemma_3 :
    ∃ KL : ℝ, 0 < KL ∧
      ∀ {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ),
        HasOrthonormalCols U →
        ∀ (T W : ℝ), 0 < T → 0 < W →
        ∀ (h : Fin n → Fin t), BucketBound U T W h →
        ∀ (y : Fin n → ℝ),
          y ∈ LinearMap.range (Matrix.mulVecLin U) → sqNorm y = 1 →
          ∀ ℓ : ℝ, 2 ≤ ℓ → ℓ ≤ 1 / W →
            unifProb (Fin n → Bool)
              {σ | KL * Real.sqrt (W * ℓ) <
                |sqNorm (sketch h σ *ᵥ light U T y) - sqNorm (light U T y)|} ≤
              Real.exp (-ℓ) := by sorry

end InputSparsity.Embed
