-- Prove2me | Theorems.Thm_NewtonGravitation_gravField_at_origin_eq_zero
-- name    : NewtonGravitation.gravField_at_origin_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T18:51:51.814839+00:00
-- url     : https://prove2.me/theorems/ee0d5b4e-3a05-49f5-8e1b-fd3e3c3ae0ff
-- title:
--   Spherical symmetry forces the field to vanish at the origin
-- statement:
--   For any mass measure invariant under all linear isometries fixing the origin, the Newtonian gravitational field at the origin is zero. Apply the symmetry hypothesis to the antipodal linear isometry y↦−y. The integrand at the origin changes sign under this map; invariance and the Bochner integral change-of-variables identity imply I=−I, hence I=0. This is valid even when the kernel is not integrable, since the integral is zero by definition in that case. It supplies the zero-radius observation case of the radial shell-averaging theorem.
-- source:
--   Prove2Me, Newton's Law of Universal Gravitation: the Shell Theorem, https://prove2.me/missions/Newton%27s_Law_of_Universal_Gravitation%3A_the_Shell_Theorem

import Definitions.Def_NewtonGravitation_Defs
import Mathlib

open MeasureTheory NewtonGravitation

theorem NewtonGravitation.gravField_at_origin_eq_zero (μ : Measure Space)
    (hμ : IsSphericallySymmetric μ) : gravField μ (0 : Space) = 0 := by sorry
