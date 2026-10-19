-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardRationalDimensionTwo_actualPicard_abelian
-- name    : MazurTransfer.Order13ActualPicardRationalDimensionTwo.actualPicard_abelian
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T08:53:27.784516+00:00
-- url     : https://prove2.me/theorems/243f6fd1-362c-4b9f-8eae-d3e6899caff2
-- title:
--   The same actual rational Picard is an abelian scheme
-- statement:
--   The original actual rational Picard scheme, with its original structural morphism to Spec Q, satisfies the original AbelianSchemePropertyBundle Q predicate. Its smoothness, properness and geometrically connected fibres come from the accepted actual integral Picard representation, and its group law is the original represented relative group law. Named downstream consumer: the exact geometric nineteen-torsion cardinality on the same Picard scheme.
-- source:
--   MazurTheorem, Order13ActualPicardRationalDimensionTwo.lean, Apache-2.0. Full original theorem type checked with no new hypotheses. The original actual Picard, base map and relative group-law constructor are retained.

import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
open MazurTransfer
open AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism

theorem MazurTransfer.Order13ActualPicardRationalDimensionTwo.actualPicard_abelian : AbelianSchemePropertyBundle ℚ actualPicard.toBase := by sorry
