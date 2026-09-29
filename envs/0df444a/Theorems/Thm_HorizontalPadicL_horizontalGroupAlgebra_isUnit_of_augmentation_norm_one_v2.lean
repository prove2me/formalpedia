-- Prove2me | Theorems.Thm_HorizontalPadicL_horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2
-- name    : HorizontalPadicL.horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:50:30.764377+00:00
-- url     : https://prove2.me/theorems/1f470d40-2cad-4994-99e0-498903c2b740
-- title:
--   Norm-one augmentation implies a unit in a horizontal group algebra
-- statement:
--   An element of the group algebra of a finite horizontal quotient over the valuation ring of C_p is a unit whenever its augmentation has p-adic norm one.
-- source:
--   Specialization of the finite p-group augmentation criterion to the valuation ring of C_p.

import Definitions.Def_KN_SeededThetaConstructionV2B

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The standard unit criterion for a group algebra of a finite `p`-group over
the valuation ring of `ℂ_p`: an element is a unit if its augmentation is a unit.
For the explicit horizontal group, being a unit in the coefficient ring is
equivalent to the displayed norm-one condition. -/
theorem horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ)
    (x : HorizontalGroupAlgebra (𝓞_ℂ_[p]).toSubring p m A)
    (haug :
      ‖((horizontalAugmentation x : (𝓞_ℂ_[p]).toSubring) : ℂ_[p])‖ = 1) :
    IsUnit x := by sorry

end HorizontalPadicL
