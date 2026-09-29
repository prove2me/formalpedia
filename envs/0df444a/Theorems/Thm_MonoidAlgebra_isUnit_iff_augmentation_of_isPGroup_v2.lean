-- Prove2me | Theorems.Thm_MonoidAlgebra_isUnit_iff_augmentation_of_isPGroup_v2
-- name    : MonoidAlgebra.isUnit_iff_augmentation_of_isPGroup_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-21T09:05:35.69816+00:00
-- url     : https://prove2.me/theorems/f4cf573e-e3bc-4a40-8854-9d2ac723769d
-- title:
--   Units in a finite p-group algebra are detected by augmentation
-- statement:
--   For a finite commutative p-group G over a commutative local ring R of residue characteristic p, an element of R[G] is a unit if and only if its augmentation is a unit in R.
-- source:
--   Corollary of Nicholson's local group-ring theorem and the standard augmentation map; https://doi.org/10.4153/CMB-1972-025-1.

import Definitions.Def_MonoidAlgebra_Augmentation
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Theorems.Thm_MonoidAlgebra_isLocalRing_of_isPGroup

set_option autoImplicit false
noncomputable section

/-- In the group ring of a finite `p`-group over a commutative local ring of
residue characteristic `p`, an element is a unit exactly when its augmentation
is a unit. This is the augmentation corollary of
`MonoidAlgebra.isLocalRing_of_isPGroup`. -/
theorem MonoidAlgebra.isUnit_iff_augmentation_of_isPGroup_v2
    {R G : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} [Fact p.Prime] [CommGroup G] [Finite G]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hG : IsPGroup p G) (x : MonoidAlgebra R G) :
    IsUnit x ↔ IsUnit (MonoidAlgebra.augmentation R G x) := by sorry
