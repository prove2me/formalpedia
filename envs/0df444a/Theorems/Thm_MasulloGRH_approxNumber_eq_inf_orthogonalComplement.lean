-- Prove2me | Theorems.Thm_MasulloGRH_approxNumber_eq_inf_orthogonalComplement
-- name    : MasulloGRH.approxNumber_eq_inf_orthogonalComplement
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:02:28.459956+00:00
-- url     : https://prove2.me/theorems/306c1124-23de-4a29-b9a8-c17d8e0354d7
-- title:
--   Variational formula for approximation numbers on a Hilbert domain
-- statement:
--   For a bounded operator $A:E\to F$ from a Hilbert space, and $m\ge1$, the $m$-th approximation number satisfies
--   $$\sigma_m(A)=\inf_{\substack{K\subset E\\ \dim K<m}}\lVert A|_{K^\perp}\rVert.$$
--   Here $K$ runs over finite-dimensional subspaces, and the restricted norm is the operator norm. This gives the infimum form of the first variational expression in Masullo’s (C.3.5.4). It applies to arbitrary bounded $A$ with normed codomain.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, pp. 700, 704, first variational expression in (C.3.5.4), using the approximation number in (C.3.6.2). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf.

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers

open Set MasulloGRH
open scoped InnerProductSpace

namespace MasulloGRH

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [CompleteSpace E]

theorem approxNumber_eq_inf_orthogonalComplement {m : ℕ} (hm : 0 < m)
    (A : E →L[𝕜] F) :
    approxNumber m A =
      sInf {r : ℝ | ∃ K : Submodule 𝕜 E, FiniteDimensional 𝕜 K ∧
        Module.finrank 𝕜 K < m ∧ r = ‖A.comp Kᗮ.subtypeL‖} := by sorry

end MasulloGRH
