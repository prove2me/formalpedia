-- Prove2me | Theorems.Thm_JaggiFW_Sparsity_lemma_4
-- name    : JaggiFW.Sparsity.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:47.111463+00:00
-- url     : https://prove2.me/theorems/05548f16-3beb-48c5-aec8-d520f4819907
-- title:
--   Lemma 4: every k-sparse simplex point has duality gap at least 2/k
-- statement:
--   For $f(x)=\sum_i x_i^2$ on the unit simplex $\Delta_n$, let $k$ be a natural number with $k<n$. Every feasible point with at most $k$ nonzero coordinates satisfies
--   $$
--   g_{f,\Delta_n}(x)\ge\frac{2}{k}
--   \qquad(x\in\Delta_n,\ \operatorname{card}(x)\le k).
--   $$
--   Thus the duality-gap guarantee cannot improve its order in the number of active coordinates for this example.
--
--   **Formalization Note** The gap is the supremum of $Df(x)[x-s]$ over $s\in\Delta_n$, equal to the paper's maximum because $k<n$ makes the compact simplex nonempty. When $k=0$, no simplex point meets the sparsity condition, so the natural-number division convention has no effect on a feasible case.
-- source:
--   Jaggi, Revisiting Frank-Wolfe: Projection-Free Sparse Convex Optimization, ICML 2013 (JMLR W&CP 28), PDF p. 5, Lemma 4

import Mathlib
import Definitions.Def_JaggiFW_Sparsity_Setting

namespace JaggiFW.Sparsity

/-- Sparse duality-gap lower bound (Lemma 4, PDF p. 5). -/
theorem lemma_4 {n : ℕ} (k : ℕ) (hk : k < n) :
    ∀ x ∈ stdSimplex ℝ (Fin n), card x ≤ k →
      2 / (k : ℝ) ≤ dualityGap sqNorm (stdSimplex ℝ (Fin n)) x := by sorry

end JaggiFW.Sparsity
