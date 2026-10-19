-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualRationalNormKernelOrdering_actual_arithmetic_norm_kernel_cards
-- name    : MazurTransfer.Order13ActualRationalNormKernelOrdering.actual_arithmetic_norm_kernel_cards
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T20:02:18.237192+00:00
-- url     : https://prove2.me/theorems/42998213-92f8-4100-b3e6-2edd7fbba7b3
-- title:
--   The arithmetic norm kernels have cardinalities one and nineteen in order
-- statement:
--   The actual arithmetic norm kernel has cardinality one, and its conjugate norm kernel has cardinality nineteen. The original affine cover parameter is retained.
-- source:
--   MazurTheorem Order13ActualRationalNormKernelOrdering.actual_arithmetic_norm_kernel_cards; exact complete original proposition retained; Apache-2.0.

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityPicardClassOrder Order13ActualDiamondPicardEndomorphisms
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.Order13ActualRationalNormKernelOrdering.actual_arithmetic_norm_kernel_cards (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) : Nat.card pi.ker = 1 ∧ Nat.card piConjugate.ker = 19 := by sorry
