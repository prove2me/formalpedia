-- Prove2me | Theorems.Thm_InputSparsity_Embed_lemma_8
-- name    : InputSparsity.Embed.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:03.763881+00:00
-- url     : https://prove2.me/theorems/ac92e3c0-f515-4b7c-92bd-57b475d290d3
-- title:
--   Lemma 8, p. 10 — fixed-vector control lifts to a whole subspace
-- statement:
--   There is an absolute constant $K_{\mathrm{sub}}>0$. Let $L\subseteq\mathbb R^n$ be a subspace of positive dimension $r$, and let $B$ be a random linear map to $\mathbb R^k$. Suppose every fixed $x\in L$ obeys
--
--   $$\Pr\!\left(\left|\|Bx\|_2^2-\|x\|_2^2\right|\le\frac{\varepsilon}{6}\|x\|_2^2\right)\ge1-\delta_{\mathrm{sub}}.$$
--
--   Then the event that the same bound with $\varepsilon$ holds for every $x\in L$ simultaneously has probability at least $1-\delta_{\mathrm{sub}}K_{\mathrm{sub}}^r$.
--
--   This is the step from a fixed input vector to a subspace embedding.
--
--   **Formalization Note** The random matrix is coordinatewise measurable on an arbitrary probability space. Positive dimension excludes the degenerate lattice-net case.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 10, Lemma 8

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, Lemma 8, p. 10: fixed-vector control lifts to a whole subspace. -/
theorem lemma_8 :
    ∃ Ksub : ℝ, 0 < Ksub ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] {n k : ℕ}
        (L : Submodule ℝ (Fin n → ℝ))
        (B : Ω → Matrix (Fin k) (Fin n) ℝ),
          (∀ i j, Measurable (fun ω => B ω i j)) →
          ∀ (ε δsub : ℝ), 0 < ε → 0 < δsub →
            1 ≤ Module.finrank ℝ L →
            (∀ x ∈ L,
              1 - δsub ≤ P.real
                {ω | |sqNorm (B ω *ᵥ x) - sqNorm x| ≤ ε / 6 * sqNorm x}) →
              1 - δsub * Ksub ^ Module.finrank ℝ L ≤ P.real
                {ω | ∀ x ∈ L,
                  |sqNorm (B ω *ᵥ x) - sqNorm x| ≤ ε * sqNorm x} := by sorry

end InputSparsity.Embed
