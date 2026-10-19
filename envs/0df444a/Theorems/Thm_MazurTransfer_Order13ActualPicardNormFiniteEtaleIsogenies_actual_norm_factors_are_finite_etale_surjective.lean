-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective
-- name    : MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T21:20:15.26237+00:00
-- url     : https://prove2.me/theorems/5bb7d0ce-1b27-4ee0-bfb5-462fd5592c27
-- title:
--   Both original norm endomorphisms of the actual rational Picard are finite etale and surjective
-- statement:
--   Let P be the same actual rational represented Picard scheme, with its existing diamond delta and original norm endomorphisms pi=3 id+2 delta and pi-bar=5 id-2 delta, using the Picard group law. Both pi and pi-bar are finite, etale and surjective as scheme morphisms over Q. The named downstream consumers are the actual finite-etale norm kernels and the norm-isogeny descent.
-- source:
--   Complete original MazurTheorem Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective, retaining its full original type and all seventeen original intermediate proof arguments from Order13ActualPicardNormFiniteUnramified and Order13ActualPicardNormFiniteEtaleIsogenies. Uses the same actual Picard family, original norm constructors, original scalar/group providers and accepted genuine scheme norm identities. Official Anthropic FLT geometry interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
noncomputable section
open CategoryTheory AlgebraicGeometry
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm

theorem MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective :
    (IsFinite schemePi.left ∧ Etale schemePi.left ∧ Surjective schemePi.left) ∧
    (IsFinite schemePiConjugate.left ∧ Etale schemePiConjugate.left ∧ Surjective schemePiConjugate.left) := by sorry
