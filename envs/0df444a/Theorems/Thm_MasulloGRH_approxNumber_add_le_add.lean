-- Prove2me | Theorems.Thm_MasulloGRH_approxNumber_add_le_add
-- name    : MasulloGRH.approxNumber_add_le_add
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:58:34.823259+00:00
-- url     : https://prove2.me/theorems/fcaa0f52-84b9-4caf-9693-1a7e53e7d6bb
-- title:
--   Corrected sum inequality for approximation numbers
-- statement:
--   For bounded linear operators $A,B:E\to F$ between normed spaces and positive integers $m,n$,
--   $$\sigma_{m+n-1}(A+B)\le \sigma_m(A)+\sigma_n(B).$$
--   The index $m+n-1$ corrects the index in Masullo’s Lemma C.3.6.3(1).
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, p. 704, Eq. (C.3.6.2) and Lemma C.3.6.3. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The same-index sum estimate is disproved at https://prove2.me/theorems/ac4831ba-e3dc-4ba2-afeb-0049ab739c30.

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers

open MasulloGRH

namespace MasulloGRH

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem approxNumber_add_le_add {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : E →L[𝕜] F) :
    approxNumber (m + n - 1) (A + B) ≤ approxNumber m A + approxNumber n B := by sorry

end MasulloGRH
