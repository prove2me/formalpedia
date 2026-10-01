-- Prove2me | Theorems.Thm_MilnorDynamics_sl2z_quotient_equiv_thrice_punctured
-- name    : MilnorDynamics.sl2z_quotient_equiv_thrice_punctured
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T21:32:19.901986+00:00
-- url     : https://prove2.me/theorems/f2a173f9-47fd-475b-be2f-62accc5c8684
-- title:
--   The modular quotient of the upper half-plane is the thrice-punctured sphere
-- statement:
--   The classical theory of the modular function identifies the quotient of the upper half-plane by SL(2,Z) with the thrice-punctured sphere: the modular lambda function lambda from H to C minus {0,1} is invariant under SL(2,Z), descends to the quotient, and induces a homeomorphism H/SL(2,Z) isomorphic to C minus {0,1}. Equivalently the j-invariant j = 256 (1 - lambda + lambda^2)^3 / (lambda^2 (1 - lambda)^2) is a biholomorphism of the quotient onto C. This identification is the genuinely hard analytic input in Milnor's Lemma 2.5 and is not formalised in Mathlib.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; Serre, Modular Functions and Dirichlet Series in Number Theory; standard theory of the modular lambda function and the j-invariant. The topological input (proper discontinuity of the modular group action) is properlyDiscontinuousSL2ZRange in Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous.

import Mathlib
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

open scoped MatrixGroups UpperHalfPlane OnePoint
open Matrix Set

namespace MilnorDynamics

/-- The classical identification of the modular quotient with the thrice-punctured sphere,
`H / SL(2,Z)` isomorphic to `C \ {0,1}`, realised by the modular lambda function
(equivalently by the `j`-invariant `256 (1 - L + L^2)^3 / (L^2 (1 - L)^2)`).  This is the
analytic heart of Milnor's Lemma 2.5: it is the step that makes the quotient
*three*-punctured rather than merely hyperbolic. -/
theorem sl2z_quotient_equiv_thrice_punctured :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel 𝒮ℒ ℍ)) 𝒮ℒ ∧
      Nonempty (Quotient (MulAction.orbitRel 𝒮ℒ ℍ) ≃ₜ {z : ℂ // z ≠ 0 ∧ z ≠ 1}) := by sorry

end MilnorDynamics
