-- Prove2me | Theorems.Thm_InputSparsity_Embed_lemma_2
-- name    : InputSparsity.Embed.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:01.86543+00:00
-- url     : https://prove2.me/theorems/17f7ca2d-f3a5-4af4-9239-7492218146fe
-- title:
--   Lemma 2, p. 8 — weighted light leverage in random buckets
-- statement:
--   Let $U\in\mathbb R^{n\times r}$ have orthonormal columns and leverage scores $u_i$. Fix $T>0$, $\delta_h>0$, and an integer $t>0$. Set $W=T\log(t/\delta_h)+r/t$. If
--
--   $$t\ge\frac{6\sum_{i:u_i\le T}u_i^2}{T^2\log(t/\delta_h)},$$
--
--   then, with probability at least $1-\delta_h$ over a uniform bucket map $h:[n]\to[t]$, every bucket contains total light leverage at most $W$.
--
--   The bound supplies the bucket event used by the light-coordinate and cross-term lemmas.
--
--   **Formalization Note** The paper sorts rows before writing the light range as $i\ge s$; the formula uses the equivalent condition $u_i\le T$. For $\delta_h\ge t$, the claimed lower probability is nonpositive and the boundary case is automatic.
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 8, Lemma 2

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Embed
open Matrix

/-- Clarkson--Woodruff, Lemma 2, p. 8: weighted light coordinates in random buckets. -/
theorem lemma_2 {n r t : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (hU : HasOrthonormalCols U) (ht : 0 < t)
    (T δh : ℝ) (hT : 0 < T) (hδh : 0 < δh)
    (hsize : 6 * (∑ i ∈ Finset.univ.filter (fun i => lev U i ≤ T),
        (lev U i) ^ 2) /
        (T ^ 2 * Real.log ((t : ℝ) / δh)) ≤ (t : ℝ)) :
    1 - δh ≤ unifProb (Fin n → Fin t)
      {h | BucketBound U T (T * Real.log ((t : ℝ) / δh) + (r : ℝ) / t) h} := by sorry

end InputSparsity.Embed
