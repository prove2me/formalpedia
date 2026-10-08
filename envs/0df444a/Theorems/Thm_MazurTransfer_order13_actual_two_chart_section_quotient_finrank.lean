-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_two_chart_section_quotient_finrank
-- name    : MazurTransfer.order13_actual_two_chart_section_quotient_finrank
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T21:25:09.837483+00:00
-- url     : https://prove2.me/theorems/35f4be79-868a-4040-b7ff-9bdb670b965b
-- title:
--   Dimension two of the actual order-13 two-chart section quotient
-- statement:
--   Let K be any field, f(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1,
--   A=K[x,y]/(y^2-f(x)), and L=A[x^-1]. The K-vector-space quotient of L by the sum of
--   the ordinary chart image A and the reciprocal chart sections p(x^-1)+q(x^-1)y*x^-3
--   has dimension exactly two. The proof identifies these with the images of the actual
--   original chart coordinate algebras and gives a linear equivalence with K^2.
--   This is the algebraic two-chart section quotient. It does not assert a comparison
--   with derived structure-sheaf H1 or a genus theorem; these are separate obligations.
--   The result applies over every field, including fibers where the curve is singular.
-- source:
--   Original affine and reciprocal chart sources by Vasily Ilin, retained whole with Apache-2.0 attribution: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . New Laurent algebra equivalence, chart-image comparison, and quotient calculation by Vas and contributors. Named downstream consumer: a faithful comparison between the actual two-chart quotient and genuine structure-sheaf H1 of curveScheme.

import Mathlib

theorem MazurTransfer.order13_actual_two_chart_section_quotient_finrank (K : Type*) [Field K] :
    let f : Polynomial K := Polynomial.X ^ 6 + 2 * Polynomial.X ^ 5 +
      Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
      4 * Polynomial.X + 1
    let q : Polynomial (Polynomial K) := Polynomial.X ^ 2 - Polynomial.C f
    let A := AdjoinRoot q
    let x : A := AdjoinRoot.of q Polynomial.X
    let y : A := AdjoinRoot.root q
    let L := Localization.Away x
    let ordinary : A →ₗ[K] L := (Algebra.algHom K A L).toLinearMap
    let coeff : Polynomial K →ₗ[K] L :=
      (Polynomial.aeval (IsLocalization.Away.invSelf x) : Polynomial K →ₐ[K] L).toLinearMap
    let reciprocal : (Polynomial K × Polynomial K) →ₗ[K] L :=
      coeff.coprod ((LinearMap.mulRight K
        (algebraMap A L y * (IsLocalization.Away.invSelf x) ^ 3)).comp coeff)
    Module.finrank K (L ⧸ (ordinary.range ⊔ reciprocal.range)) = 2 := by sorry
