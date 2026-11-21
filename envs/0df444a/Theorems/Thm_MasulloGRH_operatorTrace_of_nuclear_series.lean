-- Prove2me | Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series
-- name    : MasulloGRH.operatorTrace_of_nuclear_series
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:54:52.207116+00:00
-- url     : https://prove2.me/theorems/465a23f4-910e-4e70-b797-ccb2aca78a12
-- title:
--   Trace of an absolutely summable rank-one expansion
-- statement:
--   Expand the chosen Hilbert basis diagonal and interchange sums using Bessel's inequality and absolute convergence. Parseval gives the displayed series.
-- source:
--   Masullo, The Music of the Primes, Appendix C, Definition C.3.4.2 and Corollary C.3.5.5, frozen 20 November 2026 draft.

import Definitions.Def_MasulloGRH_HilbertNuclear
open Filter Topology

namespace MasulloGRH

theorem operatorTrace_of_nuclear_series {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (x y : ℕ → H) (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) : operatorTrace T = ∑' m, inner ℂ (x m) (y m) := by sorry

end MasulloGRH
