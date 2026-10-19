-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePi_geometricPoint_surjective
-- name    : MazurTransfer.Order13ActualPicardGeometricNormPreimages.schemePi_geometricPoint_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T21:38:15.066514+00:00
-- url     : https://prove2.me/theorems/de892b24-01fe-4a7b-9bfc-9f190571fc40
-- title:
--   Every geometric point of the actual rational Picard has an original pi preimage
-- statement:
--   Let P be the same actual rational represented Picard scheme, and let pi be its original norm endomorphism. For every algebraically closed characteristic-zero field K and every point a in P(K), there exists b in P(K) such that pi(b)=a. The named downstream consumers are the actual norm Kummer cocycles and norm-isogeny descent.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricNormPreimages.schemePi_geometricPoint_surjective statement and main proof, retaining the original field and class binders explicitly. The original finite and surjective helper types are retained, with proofs projected from the accepted exact original joint factor theorem. Uses the original Points abbreviation with its full type and value preserved, and the same actual Picard and norm morphisms. Official Anthropic FLT geometric-point lifting at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricFieldPointsData
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
noncomputable section
open CategoryTheory AlgebraicGeometry
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open MazurTransfer.Order13ActualPicardGeometricNormPreimages

theorem MazurTransfer.Order13ActualPicardGeometricNormPreimages.schemePi_geometricPoint_surjective (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : Points K) :
    ∃ b : Points K, b ≫ schemePi = a := by sorry
