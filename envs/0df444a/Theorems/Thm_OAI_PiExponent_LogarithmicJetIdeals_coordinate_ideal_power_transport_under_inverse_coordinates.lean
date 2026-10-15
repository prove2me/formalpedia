-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_ideal_power_transport_under_inverse_coordinates
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coordinate_ideal_power_transport_under_inverse_coordinates
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T18:20:39.558758+00:00
-- url     : https://prove2.me/theorems/e7f491d2-7bc6-434d-bcae-5765b40ceffd
-- title:
--   Coordinate ideal powers transport under inverse coordinates
-- statement:
--   Substituting the local jet coordinates for the polynomial variables sends membership in the coordinate monomial ideal’s nth power to membership in the corresponding local jet ideal’s nth power. This follows because substitution maps each coordinate generator to its matching local jet generator, including when an exponent is zero or n is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coordinate_ideal_power_transport_under_inverse_coordinates
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (n : ℕ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoord : Q ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n) :
    MvPolynomial.aeval (jetCoordinate c T) Q ∈ (localJetIdeal c T e) ^ n := by sorry
