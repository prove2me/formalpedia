-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actualPicard_fibre_dimension_two
-- name    : MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actualPicard_fibre_dimension_two
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T10:09:33.505016+00:00
-- url     : https://prove2.me/theorems/9b6d44c5-0946-4429-9531-cb86bd140780
-- title:
--   The actual rational Picard has two-dimensional fibres
-- statement:
--   Every fibre of the designated Picard scheme of the literal order-13 curve over the rational field has topological Krull dimension two. The scheme is the same represented Picard used for the actual diamond and norm endomorphisms. No dimension hypothesis is assumed.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionCardinality.actualPicard_fibre_dimension_two; exact original checked contract, with rational dimension obtained from connected fibres and algebraically closed base change.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardDesignation
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism

theorem MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actualPicard_fibre_dimension_two (s : Spec (CommRingCat.of ℚ)) :
    topologicalKrullDim ↥(actualPicard.toBase.base ⁻¹' {s}) = 2 := by sorry
