-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_affine_smooth_relativeDimension_one
-- name    : MazurTransfer.order13_actual_affine_smooth_relativeDimension_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T21:49:51.677019+00:00
-- url     : https://prove2.me/theorems/6080e9f4-8dd4-4339-88de-5c10f4165f77
-- title:
--   Actual order-13 affine curve is smooth of relative dimension one
-- statement:
--   For every characteristic-zero field K, the actual affine curve y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1 is smooth of relative dimension one over K. The proof constructs a genuine free rank-one Kaehler differential module, proves local standard smoothness of dimension one, and applies the associated genuine scheme morphism property. Its complete companion sources also establish relative-dimension-one smoothness of the reciprocal chart and the original glued curve. No genus or Jacobian assertion is assumed.
-- source:
--   Original affine and reciprocal chart sources by Vasily Ilin, retained whole with Apache-2.0 attribution: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . New differential module construction and relative dimension proofs by Vas and contributors. Named downstream consumer: the actual order-13 curveToBase and the official Anthropic FLT scheme-to-genus comparison.

import Mathlib

theorem MazurTransfer.order13_actual_affine_smooth_relativeDimension_one (K : Type*) [Field K] [CharZero K] :
    let f : Polynomial K := Polynomial.X ^ 6 + 2 * Polynomial.X ^ 5 +
      Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
      4 * Polynomial.X + 1
    let A := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f)
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K A))) := by sorry
