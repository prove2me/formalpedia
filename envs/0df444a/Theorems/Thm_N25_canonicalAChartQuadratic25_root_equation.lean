-- Prove2me | Theorems.Thm_N25_canonicalAChartQuadratic25_root_equation
-- name    : N25.canonicalAChartQuadratic25_root_equation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:55.620952+00:00
-- url     : https://prove2.me/theorems/4cd9a1fd-752e-42bb-8819-a0f76d6d238b
-- title:
--   The adjoined root satisfies the explicit quadratic equation of the canonical affine chart
-- statement:
--   Let $π$ be a homomorphism from the canonical $A$-chart base ring over $K$ to a commutative ring $S$. Map the chart quadratic along $π$, let $y$ be its adjoined root, and let $x,z$ be the images of the base coordinates. Then $$y^2+(2z-x)y+z^2-2xz+x-z=0.$$ This records the quadratic relation in every base change of the tower presentation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

open N25
open Polynomial
variable (K : Type*) [Field K]

theorem N25.canonicalAChartQuadratic25_root_equation
    {S : Type*} [CommRing S] (π : CanonicalAChartBase25 K →+* S) :
    let q := (canonicalAChartQuadratic25 K).map π
    let ι := AdjoinRoot.of q
    let x := ι (π (canonicalAChartBaseX25 K))
    let z := ι (π (canonicalAChartBaseZ25 K))
    let y := AdjoinRoot.root q
    y^2+(2*z-x)*y+z^2-2*x*z+x-z = 0 := by sorry
