-- Prove2me | Theorems.Thm_MazurTransfer_order13_mixed_quadratic_unit_and_smoothness_certificates
-- name    : MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T02:21:45.584915+00:00
-- url     : https://prove2.me/theorems/0c75a8ce-bea0-4ba9-8299-35bb7c399a2c
-- statement:
--   The literal ordinary and reciprocal mixed quadratic coordinate algebras have the original Jacobian-unit witnesses and are genuinely smooth over every commutative base ring in which 117 and 39, respectively, are units. The complete original hypotheses and all seventeen proof helper types are retained and checked. The named downstream consumer is the actual pair of dyadic affine charts.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalPolynomialsAndJacobianCoefficientData20261019
import Definitions.Def_MazurTransfer_MixedQuadraticOriginalCoordinateEquationAndJacobianData20261019
import Theorems.Thm_MazurTransfer_order13_mixed_quadratic_integral_jacobian_certificates
import Theorems.Thm_MazurTransfer_mixed_quadratic_coordinate_smooth
noncomputable section
open Polynomial MazurTransfer.MixedQuadraticCoordinateJacobian MazurTransfer.Order13MixedQuadraticJacobianCertificates
universe u v

theorem MazurTransfer.order13_mixed_quadratic_unit_and_smoothness_certificates :
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (117 : R)) ,
    ∃ a b : CoordinateRing R (ordinaryH R) (ordinaryF R),
      a * partialX R (ordinaryH R) (ordinaryF R) + b * partialY R (ordinaryH R) (ordinaryF R) = 1) ∧
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (117 : R)) ,
    Algebra.Smooth R (CoordinateRing R (ordinaryH R) (ordinaryF R))) ∧
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (39 : R)) ,
    ∃ a b : CoordinateRing R (reciprocalH R) (reciprocalF R),
      a * partialX R (reciprocalH R) (reciprocalF R) + b * partialY R (reciprocalH R) (reciprocalF R) = 1) ∧
    (∀ (R : Type u) [CommRing R] (hu : IsUnit (39 : R)) ,
    Algebra.Smooth R (CoordinateRing R (reciprocalH R) (reciprocalF R))) := by sorry
