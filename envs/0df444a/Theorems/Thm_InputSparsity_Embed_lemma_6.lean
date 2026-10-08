-- Prove2me | Theorems.Thm_InputSparsity_Embed_lemma_6
-- name    : InputSparsity.Embed.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:00.212389+00:00
-- url     : https://prove2.me/theorems/fa4af6a8-7487-450b-9f6d-a1b1c247e646
-- title:
--   Lemma 6, pp. 9–10 — concentration of the heavy-light cross term
-- statement:
--   There is an absolute constant $K_C>0$. Let $U$ have orthonormal columns, let $y$ be a unit vector in its column space, and fix a bucket map $h$ satisfying both the light-bucket event $E_h$ and the no-heavy-collision event $E_B$. For $0<\delta_C\le e^{-1}$,
--
--   $$\Pr_{\sigma}\!\left(\left|\langle\Phi D y_H,\Phi D y_L\rangle\right|>K_C\sqrt{W\log(1/\delta_C)}\right)\le\delta_C.$$
--
--   The estimate controls the interaction between the heavy and light parts of a fixed vector.
--
--   **Formalization Note** The probability is over signs after fixing $h$. The range $\delta_C\le e^{-1}$ is needed for the printed moment argument; the paper's proof has a reversed probability sign at this step.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, pp. 9–10, Lemma 6

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, Lemma 6, pp. 9--10: concentration of the heavy-light cross term. -/
theorem lemma_6 :
    ∃ KC : ℝ, 0 < KC ∧
      ∀ {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ),
        HasOrthonormalCols U →
        ∀ (T W : ℝ), 0 < T → 0 < W →
        ∀ (h : Fin n → Fin t), BucketBound U T W h →
          PerfectOnHeavy U T h →
        ∀ (y : Fin n → ℝ),
          y ∈ LinearMap.range (Matrix.mulVecLin U) → sqNorm y = 1 →
          ∀ δC : ℝ, 0 < δC → δC ≤ Real.exp (-1) →
            unifProb (Fin n → Bool)
              {σ | KC * Real.sqrt (W * Real.log (1 / δC)) <
                |(sketch h σ *ᵥ heavy U T y) ⬝ᵥ
                  (sketch h σ *ᵥ light U T y)|} ≤ δC := by sorry

end InputSparsity.Embed
