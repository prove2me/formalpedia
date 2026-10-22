-- Prove2me | Theorems.Thm_NisetNoGo_GECC_no_go_theorem
-- name    : NisetNoGo.GECC.no_go_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:33.245391+00:00
-- url     : https://prove2.me/theorems/89607d88-2622-4070-bc46-84eb38039ea9
-- title:
--   Theorem, (11) — Gaussian codes cannot lower entanglement degradation
-- statement:
--   Let $T=(M,N)$ be any completely positive single-mode Gaussian channel. A Gaussian error-correcting code $G(n,E,D)$ uses $n\ge1$ copies of $T$, $n-1$ vacuum ancillas, and symplectic Gaussian encoding and decoding operations $S_E,S_D$ on all $n$ modes; it keeps the first output mode. Write $T_{GC}=(M_{GC},N_{GC})$ for its resulting channel. Then
--
--   $$D[T]\le D[T_{GC}].$$
--
--   Thus no code of this form reduces the channel's entanglement degradation. The result covers all completely positive single-mode Gaussian channels, including singular and negative-determinant cases.
--
--   **Formalization Note** The definition of $D$ saturates at $1$ when $1+\det M=0$, the paper's infinite-quotient reading. A literal real division in Lean would return zero there and misstate (11). Gaussian displacements are omitted because they do not alter covariance matrices.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, p. 3, Theorem, (11); code G(n,E,D) of Fig. 1, p. 2

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13

namespace NisetNoGo.GECC

theorem no_go_theorem (n : ℕ) [NeZero n]
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hT : IsCPChannel M N)
    (SE SD : Matrix (ModeQuadrature (Fin n)) (ModeQuadrature (Fin n)) ℝ)
    (hE : IsSymplecticMat SE) (hD : IsSymplecticMat SD) :
    entDeg M N ≤ entDeg (geccM n M SE SD) (geccN n M N SE SD) := by sorry

end NisetNoGo.GECC
