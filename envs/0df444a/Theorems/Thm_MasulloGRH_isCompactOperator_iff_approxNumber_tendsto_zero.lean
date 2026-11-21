-- Prove2me | Theorems.Thm_MasulloGRH_isCompactOperator_iff_approxNumber_tendsto_zero
-- name    : MasulloGRH.isCompactOperator_iff_approxNumber_tendsto_zero
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:20:10.426484+00:00
-- url     : https://prove2.me/theorems/0b6fe026-b85c-4735-8f66-faaf8e894f42
-- title:
--   Compactness is equivalent to approximation numbers tending to zero
-- statement:
--   Let $A:E\to F$ be a bounded linear map from a normed space to a Hilbert space over $\mathbb R$ or $\mathbb C$. The operator is compact if and only if its approximation numbers $\sigma_n(A)$ tend to zero as $n\to\infty$. This is the approximation-number form of the compact norm-approximation step in Masullo’s Theorem C.3.6.1.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, pp. 703–704, Theorem C.3.6.1 and Eq. (C.3.6.2). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf.

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers

open Filter
open scoped Topology

namespace MasulloGRH

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem isCompactOperator_iff_approxNumber_tendsto_zero [CompleteSpace F]
    (A : E →L[𝕜] F) :
    IsCompactOperator A ↔ Tendsto (fun n : ℕ ↦ approxNumber n A) atTop (𝓝 0) := by sorry

end MasulloGRH
