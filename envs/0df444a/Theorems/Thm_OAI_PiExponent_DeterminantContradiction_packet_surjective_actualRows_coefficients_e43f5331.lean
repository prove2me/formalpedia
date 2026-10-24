-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_actualRows_coefficients_e43f5331
-- name    : OAI.PiExponent.DeterminantContradiction.packet_surjective_actualRows_coefficients_e43f5331
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:40:25.258027+00:00
-- url     : https://prove2.me/theorems/9c19e222-9137-49f2-983c-8b68880f1612
-- title:
--   Independent actual rows realize arbitrary row values
-- statement:
--   If the actual matrix rows are linearly independent, every assignment of complex values to those rows is a linear combination of the matrix columns.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.packet_surjective_actualRows_coefficients_e43f5331
    (nu : Real) (d : FixedData nu) (H : Real)
    (hrows : LinearIndependent Complex (fun rho : Row d H => actualMatrix d H rho))
    (values : Row d H → Complex) :
    ∃ a : Column d H → Complex, ∀ rho : Row d H,
      ∑ c : Column d H, a c * actualMatrix d H rho c = values rho := by sorry
