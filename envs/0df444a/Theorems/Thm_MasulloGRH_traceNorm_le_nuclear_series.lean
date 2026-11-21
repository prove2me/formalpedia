-- Prove2me | Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series
-- name    : MasulloGRH.traceNorm_le_nuclear_series
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:54:51.318757+00:00
-- url     : https://prove2.me/theorems/885ae79f-e5bf-48b3-b708-c38c8abfcd9b
-- title:
--   Trace norm bounded by the cost of a nuclear expansion
-- statement:
--   An absolutely summable expansion by rank-one operators bounds the trace norm by the sum of the products of the vector norms. Applied to the projected differences, this permits dominated convergence.
-- source:
--   Masullo, The Music of the Primes, Appendix C, Definition C.3.4.2 and Corollary C.3.5.5, frozen 20 November 2026 draft.

import Definitions.Def_MasulloGRH_HilbertNuclear
open Filter Topology

namespace MasulloGRH

theorem traceNorm_le_nuclear_series {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (x y : ℕ → H) (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) : traceNorm T ≤ ∑' m, ‖x m‖ * ‖y m‖ := by sorry

end MasulloGRH
