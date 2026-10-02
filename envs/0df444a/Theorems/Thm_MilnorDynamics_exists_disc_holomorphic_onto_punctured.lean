-- Prove2me | Theorems.Thm_MilnorDynamics_exists_disc_holomorphic_onto_punctured
-- name    : MilnorDynamics.exists_disc_holomorphic_onto_punctured
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:40:45.560686+00:00
-- url     : https://prove2.me/theorems/92d7514b-f00e-4db1-bfc3-1668dff66370
-- title:
--   A holomorphic map of the open unit disc onto the thrice-punctured plane, omitting both punctures
-- statement:
--   There is a complex differentiable function p on the open unit disc whose values avoid 0 and 1 and whose total range is exactly the twice-punctured plane: p of the open disc equals C minus {0,1}. A concrete witness is the modular lambda function from the upper half-plane to C minus {0,1}, pulled back along the Cayley bijection from the disc to the half-plane. Holomorphy is the standard fact that lambda is holomorphic on H; the range statement is the classical surjectivity of the modular lambda function, equivalently that the j-invariant is onto the complex plane. No covering property is asserted here: that is a separate theorem.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; the classical theory of the modular lambda function and the j-invariant (Serre, Modular Functions and Dirichlet Series in Number Theory). This is the analytic content of the lemma, isolating holomorphy, puncture avoidance, and surjectivity from the covering property.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The analytic core of Milnor's Lemma 2.5.  There is a holomorphic map
`p : D -> C \ {0,1}` on the open unit disc which omits both punctures and whose range
is exactly `C \ {0,1}`.  A concrete witness is the modular lambda function
`lambda : H -> C \ {0,1}` composed with the Cayley bijection `c : D -> H`; the range
statement is the classical surjectivity of lambda (equivalently, that the j-invariant
is onto `C`).  No covering property is claimed here. -/
theorem exists_disc_holomorphic_onto_punctured :
    exists p : ℂ -> ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) /\
      exists hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        Set.range p = {0, 1}ᶜ := by sorry

end MilnorDynamics
