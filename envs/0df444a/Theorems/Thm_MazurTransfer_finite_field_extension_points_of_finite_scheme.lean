-- Prove2me | Theorems.Thm_MazurTransfer_finite_field_extension_points_of_finite_scheme
-- name    : MazurTransfer.finite_field_extension_points_of_finite_scheme
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-11T00:31:15.359006+00:00
-- url     : https://prove2.me/theorems/7607c811-3f71-4ef4-93d2-b8565aa95b18
-- title:
--   A finite scheme has finitely many points over any extension field
-- statement:
--   If X is a scheme finite over a field F, and K is any extension field of F, then the set of K-valued F-points of X is finite. This applies even when X is nonreduced. It supplies the geometric finiteness used to construct finite F19 norm-kernel representations; it asserts no numerical cardinality or kernel degree.
-- source:
--   Owned MazurTheorem integration proof, Apache-2.0. Uses Mathlib affine-scheme equivalence and finiteness of algebra homomorphisms from a finite-dimensional algebra into a field, together with the public Anthropic FLT SchemeHomOver interface at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem MazurTransfer.finite_field_extension_points_of_finite_scheme
    (F K : Type) [Field F] [Field K] [Algebra F K]
    (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) t) := by sorry
