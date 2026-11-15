-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_GaussianPoissonSeries_dependentProductMass_hasSum
-- name    : InfoLossLAR.WorstCase.GaussianPoissonSeries.dependentProductMass_hasSum
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:49:13.304195+00:00
-- url     : https://prove2.me/theorems/b98f006f-4655-4174-80cd-3ec5bff63c0c
-- title:
--   The complete finite product of summable masses has the product total mass
-- statement:
--   For any source type and any finite number n of coordinates, suppose each coordinate has a nonnegative summable real mass function. Then the complete joint product mass on n-tuples has a HasSum equal to the product of the individual total masses. The mass may depend on the coordinate. This is a statement about the full joint law, with no finite-source or independent-marginal shortcut and no algorithmic claim.
-- source:
--   Exact existing complete proof InfoLossLAR.WorstCase.GaussianPoissonSeries.dependentProductMass_hasSum in Solutions/RegevBridgeDependentProductMass.lean, frozen source SHA 35d70b887158c65e83faa69ff18bac2ef1271fdc33e1b8c9bb95f81b0ada9bb0. Official Lean syntax/info-tree declaration byte ranges are used; only the root binding is renamed to global solution and an unused import closure is removed. No new mathematical argument.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

theorem dependentProductMass_hasSum {Index : Type*} (dimension : ℕ)
    (mass : Fin dimension → Index → ℝ)
    (hnonnegative : ∀ index value,0 ≤ mass index value) (hsummable : ∀ index,Summable (mass index)) :
    HasSum (fun word : Fin dimension → Index => ∏ index,mass index (word index))
      (∏ index,∑' value,mass index value) := by sorry

end InfoLossLAR.WorstCase.GaussianPoissonSeries
