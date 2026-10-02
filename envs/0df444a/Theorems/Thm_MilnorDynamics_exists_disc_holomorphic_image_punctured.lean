-- Prove2me | Theorems.Thm_MilnorDynamics_exists_disc_holomorphic_image_punctured
-- name    : MilnorDynamics.exists_disc_holomorphic_image_punctured
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T22:10:51.461717+00:00
-- url     : https://prove2.me/theorems/d007452c-adb2-4c38-bc2b-88168675ea89
-- title:
--   A holomorphic map of the open unit disc onto the thrice-punctured sphere
-- statement:
--   There is a complex differentiable function p on the open unit disc whose values avoid 0 and 1 and whose image of the open disc is exactly the twice-punctured plane: p of the open unit disc equals C minus {0,1}. A concrete witness is the modular lambda function from the upper half-plane to C minus {0,1}, pulled back along the Cayley bijection from the disc to the half-plane. Holomorphy is the standard fact that lambda is holomorphic on the upper half-plane. The image statement is the classical surjectivity of the modular lambda function, equivalently that the j-invariant is onto the complex plane. Note the image is taken over the open disc itself, which is exactly what Lemma 2.5 requires: the covering map has domain the disc, so surjectivity must be attained inside the disc rather than somewhere in the plane. No covering property is asserted here.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; the classical theory of the modular lambda function and the j-invariant (Serre, Modular Functions and Dirichlet Series in Number Theory). This is the analytic content of the lemma, isolating holomorphy, puncture avoidance, and surjectivity of the disc map from the covering property.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The analytic core of Milnor's Lemma 2.5, stated on the image of the disc.  There is
a holomorphic map `p` on the open unit disc which omits both punctures and whose image
of the disc is exactly `C \ {0,1}`.  A concrete witness is the modular lambda function
`lambda : H -> C \ {0,1}` composed with the Cayley bijection `c : D -> H`; the image
statement is the classical surjectivity of lambda (equivalently, that the j-invariant is
onto `C`), and it is the surjectivity of the DISC map, not merely of the ambient map,
that Lemma 2.5 needs.  No covering property is claimed here. -/
theorem exists_disc_holomorphic_image_punctured :
    exists p : ℂ -> ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) /\
      exists hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        p '' (Metric.ball 0 1) = {0, 1}ᶜ := by sorry

end MilnorDynamics
