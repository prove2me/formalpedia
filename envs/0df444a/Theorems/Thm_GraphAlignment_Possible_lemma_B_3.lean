-- Prove2me | Theorems.Thm_GraphAlignment_Possible_lemma_B_3
-- name    : GraphAlignment.Possible.lemma_B_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:18.668403+00:00
-- url     : https://prove2.me/theorems/c464a6de-b3b3-49a2-99af-0be983b5f957
-- title:
--   Lemma B.3, p. 23 — powers of a 2×2 matrix with distinct eigenvalues
-- statement:
--   Let $M$ be a $2\times 2$ matrix over a field whose eigenvalues are $\alpha$ and $\beta$, that is, whose characteristic polynomial is $(X-\alpha)(X-\beta)$. If $\alpha \ne \beta$, then for every $n \ge 1$,
--   $$M^n = \alpha^n\,\frac{M - \beta I}{\alpha - \beta} + \beta^n\,\frac{M - \alpha I}{\beta - \alpha}.$$
--
--   The formula is used to compute the moment generating function of a cyclic sum of correlated edge indicators (Lemma B.2) through powers of a $2\times 2$ transfer matrix.
--
--   **Formalization Note** The field is arbitrary (the paper does not name one; the application is real). "Eigenvalues $\alpha$ and $\beta$" is the factorisation of `Matrix.charpoly`.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 23, Lemma B.3

import Mathlib

namespace GraphAlignment.Possible

open Polynomial in
theorem lemma_B_3 {𝕜 : Type*} [Field 𝕜] (M : Matrix (Fin 2) (Fin 2) 𝕜) (α β : 𝕜)
    (hM : M.charpoly = (X - C α) * (X - C β)) (hαβ : α ≠ β) (n : ℕ) (hn : 1 ≤ n) :
    M ^ n = (α ^ n / (α - β)) • (M - β • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) +
      (β ^ n / (β - α)) • (M - α • (1 : Matrix (Fin 2) (Fin 2) 𝕜)) := by sorry

end GraphAlignment.Possible
