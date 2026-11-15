-- Prove2me | Theorems.Thm_MazurP23_inertia_smul_eq_self_of_not_dvd_discr
-- name    : MazurP23.inertia_smul_eq_self_of_not_dvd_discr
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:10:05.687277+00:00
-- url     : https://prove2.me/theorems/fae2d732-57a9-4294-b951-d4777ce05466
-- title:
--   Inertia acts trivially on torsion at good primes
-- statement:
--   Promoted from the Frey proof (helper tw_unramified_good): if q does not divide the discriminant, inertia at q fixes the p-power torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_ValuationSubring_ReduceAt
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23
theorem inertia_smul_eq_self_of_not_dvd_discr (W : WeierstrassCurve ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hgood : ¬ (ℓ : ℤ) ∣ W.Δ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    {n : ℕ} (hn : ¬ ℓ ∣ n)
    (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hy : n • y = 0) :
    τ • y = y := by sorry
end MazurP23
