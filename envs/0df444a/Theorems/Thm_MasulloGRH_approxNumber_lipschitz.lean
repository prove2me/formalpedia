-- Prove2me | Theorems.Thm_MasulloGRH_approxNumber_lipschitz
-- name    : MasulloGRH.approxNumber_lipschitz
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:58:39.968488+00:00
-- url     : https://prove2.me/theorems/7a50ff1c-1554-4d8f-ad1c-890202294032
-- title:
--   Approximation numbers are 1-Lipschitz in operator norm
-- statement:
--   For bounded linear operators $A,B:E\to F$ between normed spaces and an integer $m\ge1$,
--   $$\lvert \sigma_m(A)-\sigma_m(B)\rvert\le\lVert A-B\rVert.$$
--   This is Masullo’s Lemma C.3.6.3(2), with the same index in both approximation numbers.
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

theorem approxNumber_lipschitz {m : ℕ} (hm : 0 < m) (A B : E →L[𝕜] F) :
    |approxNumber m A - approxNumber m B| ≤ ‖A - B‖ := by sorry

end MasulloGRH
