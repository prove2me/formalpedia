-- Prove2me | Theorems.Thm_InputSparsity_Embed_lemma_5
-- name    : InputSparsity.Embed.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:02.322369+00:00
-- url     : https://prove2.me/theorems/5f1d935d-f86a-42b4-ab67-af9e57af2f10
-- title:
--   Lemma 5, p. 9 — collision probability and exact preservation of heavy coordinates
-- statement:
--   Fix a set of heavy coordinates, containing $s-1$ indices, and a positive bucket count $t$. If $E_B$ is the event that distinct heavy indices are sent to distinct buckets, then
--
--   $$1-\Pr_h(E_B)\le\frac{s^2}{t}.$$
--
--   On $E_B$, every vector supported on the heavy coordinates retains its squared Euclidean norm under $\Phi D$, for every sign choice.
--
--   This separates the collision risk from the deterministic norm identity used later.
--
--   **Formalization Note** The heavy set is defined by leverage exceeding $T$, so $s=|H|+1$. The paper's phrase “for all $i,i'<s$” is read with the implicit distinctness condition $i\ne i'$.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 9, Lemma 5

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, Lemma 5, p. 9: distinct heavy coordinates avoid collisions and retain their norm. -/
theorem lemma_5 {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (T : ℝ) (ht : 0 < t) :
    1 - unifProb (Fin n → Fin t) {h | PerfectOnHeavy U T h} ≤
        (((Finset.univ.filter (fun i : Fin n => T < lev U i)).card + 1 : ℕ) : ℝ) ^ 2 / t ∧
      ∀ (h : Fin n → Fin t), PerfectOnHeavy U T h →
        ∀ (σ : Fin n → Bool) (y : Fin n → ℝ),
          sqNorm (heavy U T y) = sqNorm (sketch h σ *ᵥ heavy U T y) := by sorry

end InputSparsity.Embed
