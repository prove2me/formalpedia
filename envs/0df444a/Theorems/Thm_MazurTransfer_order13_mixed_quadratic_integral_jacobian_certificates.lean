-- Prove2me | Theorems.Thm_MazurTransfer_order13_mixed_quadratic_integral_jacobian_certificates
-- name    : MazurTransfer.order13_mixed_quadratic_integral_jacobian_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T02:17:52.796611+00:00
-- url     : https://prove2.me/theorems/e7eeb1f7-59b3-4591-a06c-7928943ce3de
-- statement:
--   The literal ordinary and reciprocal mixed quadratic equations have the original integral Jacobian identities with constants 117 and 39. The identities hold over every commutative ring, including residue characteristic two. The named downstream consumer is smoothness of the actual dyadic affine charts.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
noncomputable section
open Polynomial MazurTransfer.Order13MixedQuadraticJacobianCertificates
universe u

theorem MazurTransfer.order13_mixed_quadratic_integral_jacobian_certificates :
    (∀ (R : Type u) [CommRing R] (x y : R)
    (hrel : y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - (x * (x + 1)) = 0) ,
    (ordinaryB0 R x + ordinaryB1 R x * y) * ((3 * x ^ 2 + 2 * x) * y - (2 * x + 1)) +
      (ordinaryC0 R x + ordinaryC1 R x * y) * (2 * y + (x ^ 3 + x ^ 2 + 1)) = 117) ∧
    (∀ (R : Type u) [CommRing R] (x y : R)
    (hrel : y ^ 2 + (1 + x + x ^ 3) * y - (x ^ 4 + x ^ 5) = 0) ,
    (reciprocalB0 R x + reciprocalB1 R x * y) * ((1 + 3 * x ^ 2) * y - (4 * x ^ 3 + 5 * x ^ 4)) +
      (reciprocalC0 R x + reciprocalC1 R x * y) * (2 * y + (1 + x + x ^ 3)) = 39) := by sorry
