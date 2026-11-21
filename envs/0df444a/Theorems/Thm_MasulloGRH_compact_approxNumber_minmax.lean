-- Prove2me | Theorems.Thm_MasulloGRH_compact_approxNumber_minmax
-- name    : MasulloGRH.compact_approxNumber_minmax
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:13:59.150842+00:00
-- url     : https://prove2.me/theorems/7849ed50-c737-4214-8b44-2a900aed4f95
-- title:
--   Compact attainment of the approximation-number min–max formulas
-- statement:
--   Let $A:E\to F$ be a compact operator between complex Hilbert spaces and let $n=m+1$ be at most the dimension of $E$. Both variational expressions for the $n$-th approximation number are attained:
--   $$
--   \sigma_n(A)
--    =\min_{\dim K=m}\lVert A|_{K^\perp}\rVert
--    =\max_{\dim V=n}\min_{\substack{x\in V\\ \lVert x\rVert=1}}\lVert Ax\rVert.
--   $$
--   The statement provides an optimizing pair $K\subset V$. The norm on the orthogonal complement is the operator norm. The lower estimate for all vectors in $V$ and the unit-vector upper estimate in every $n$-dimensional plane give the second expression. This is the compact attainment in Masullo’s equation (C.3.5.4).
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, p. 700, Lemma C.3.5.3(3), Eq. (C.3.5.4), with approximation numbers as defined on p. 704 in (C.3.6.2). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf.

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers

open Set Module
open scoped InnerProductSpace

namespace MasulloGRH

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem compact_approxNumber_minmax (A : E →L[ℂ] F) (hA : IsCompactOperator A)
    (m : ℕ) (hm : ((m + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ E) :
    ∃ K V : Submodule ℂ E, FiniteDimensional ℂ K ∧ FiniteDimensional ℂ V ∧
      finrank ℂ K = m ∧ finrank ℂ V = m + 1 ∧ K ≤ V ∧
      ‖A.comp Kᗮ.subtypeL‖ = approxNumber (m + 1) A ∧
      (∀ x ∈ V, approxNumber (m + 1) A * ‖x‖ ≤ ‖A x‖) ∧
      ∀ W : Submodule ℂ E, FiniteDimensional ℂ W → finrank ℂ W = m + 1 →
        ∃ x : E, x ∈ W ∧ ‖x‖ = 1 ∧ ‖A x‖ ≤ approxNumber (m + 1) A := by sorry

end MasulloGRH
