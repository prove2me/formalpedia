-- Prove2me | Theorems.Thm_N25_canonicalAChartLinearRemainder25_mk
-- name    : N25.canonicalAChartLinearRemainder25_mk
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:47.399432+00:00
-- url     : https://prove2.me/theorems/cccefe23-2813-48f5-b613-932483aeb5b3
-- title:
--   The chart's linear remainder has an explicit expression in the quadratic root
-- statement:
--   Under a ring map $π$ from the canonical $A$-chart base ring to a commutative ring $S$, let $q$ be the mapped quadratic, let $y$ be its adjoined root, and let $x,z$ be the mapped base coordinates. The image of the linear remainder in $S[Y]/(q)$ is $$ (xz+x+z)y+z(z-1-x^2).$$ This formula is the input for the regularity checks in the tower ring.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

open N25
open Polynomial
variable (K : Type*) [Field K]

theorem N25.canonicalAChartLinearRemainder25_mk
    {S : Type*} [CommRing S] (π : CanonicalAChartBase25 K →+* S) :
    let q := (canonicalAChartQuadratic25 K).map π
    let ι := AdjoinRoot.of q
    let x := ι (π (canonicalAChartBaseX25 K))
    let z := ι (π (canonicalAChartBaseZ25 K))
    let y := AdjoinRoot.root q
    AdjoinRoot.mk q ((canonicalAChartLinearRemainder25 K).map π) =
      (x*z+x+z)*y+z*(z-1-x^2) := by sorry
