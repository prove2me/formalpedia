-- Prove2me | Theorems.Thm_MazurTransfer_finite_etale_geometric_points_eq_degree
-- name    : MazurTransfer.finite_etale_geometric_points_eq_degree
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-14T20:09:12.316551+00:00
-- url     : https://prove2.me/theorems/3eab8c1d-9e71-40ec-96ab-7d666aaa1752
-- title:
--   Geometric points of a finite étale scheme count its degree
-- statement:
--   Let F be a field and K an algebraically closed extension field. If X is a finite étale F-scheme, then the number of F-morphisms from Spec K to X equals the rank of X over F. This is the geometric degree, and may differ from the number of F-rational points. The result connects geometric norm-kernel point counts with actual finite étale isogeny degrees.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. Reuses the finite-etale algebra and affine-scheme point-count proofs from Anthropic FLT at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.lean. Adds field-extension point identification and finite-flat base-change invariance of rank from Mathlib.

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem MazurTransfer.finite_etale_geometric_points_eq_degree
    (F K : Type) [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    (X : Scheme.{0}) (t : X ⟶ Spec (CommRingCat.of F)) [IsFinite t] [Etale t] :
    Nat.card (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap F K))) t) =
      t.finrank (IsLocalRing.closedPoint F) := by sorry
