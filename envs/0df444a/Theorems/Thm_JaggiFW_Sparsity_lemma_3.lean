-- Prove2me | Theorems.Thm_JaggiFW_Sparsity_lemma_3
-- name    : JaggiFW.Sparsity.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:30.324008+00:00
-- url     : https://prove2.me/theorems/5e2ca365-d20d-41bf-891c-8c895d3955fd
-- title:
--   Lemma 3: the minimum squared norm of a k-sparse simplex point is 1/k
-- statement:
--   Let $1\le k\le n$. Among points $x$ of the unit simplex $\Delta_n$ with at most $k$ nonzero coordinates, the minimum squared Euclidean norm exists and is
--   $$
--   \min_{x\in\Delta_n,\ \operatorname{card}(x)\le k}\sum_i x_i^2=\frac1k.
--   $$
--   This is the sparse primal objective bound used in the paper's lower bound.
--
--   **Formalization Note** The formal statement uses an attained minimum, including an attaining sparse point, so it preserves the paper's “min” rather than merely an infimum.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), PDF p. 5, Lemma 3

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

namespace JaggiFW.Sparsity

/-- Sparse minimum of the quadratic objective (Lemma 3, PDF p. 5). -/
theorem lemma_3 {n : ℕ} (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    IsLeast {r : ℝ | ∃ x ∈ stdSimplex ℝ (Fin n), card x ≤ k ∧ r = sqNorm x}
      (1 / (k : ℝ)) := by sorry

end JaggiFW.Sparsity
