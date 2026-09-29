-- Prove2me | Theorems.Thm_HorizontalPadicL_seededEulerFactors_areUnits_v4
-- name    : HorizontalPadicL.seededEulerFactors_areUnits_v4
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:57:36.820065+00:00
-- url     : https://prove2.me/theorems/7a4359c1-3712-40a6-a424-5f75c98e156f
-- title:
--   Euler factors in the clean faithful theta system are units
-- statement:
--   Every Euler factor in the faithful finite theta system is a unit. Its augmentation has norm one by the orderly-prime condition, and the finite p-group group-algebra unit criterion lifts this to the Euler factor itself.
--
--   This is the clean-spine replacement used to remove deprecated definition bundles from the live graph.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Corollary 3.6, Definition 5.3, Corollary 5.4, Theorem 5.9, Corollary 5.10 and Corollary 5.17.

import Definitions.Def_KN_SeededThetaConstructionV2B
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The orderly-prime calculation makes every Euler factor in the faithful
theta system a unit. -/
theorem seededEulerFactors_areUnits_v4
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel) (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (Θ : SeededFiniteThetaDataV3 L) :
    Θ.HasUnitEulerFactors := by
  sorry

end HorizontalPadicL
