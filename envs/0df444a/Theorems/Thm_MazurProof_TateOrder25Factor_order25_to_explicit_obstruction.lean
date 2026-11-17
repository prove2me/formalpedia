-- Prove2me | Theorems.Thm_MazurProof_TateOrder25Factor_order25_to_explicit_obstruction
-- name    : MazurProof.TateOrder25Factor.order25_to_explicit_obstruction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:55.995349+00:00
-- url     : https://prove2.me/theorems/66202143-c70f-4332-8f1a-cd642d9517b4
-- title:
--   A rational point of order $25$ implies the explicit Tate obstruction
-- statement:
--   Let $E/ℚ$ be an elliptic curve and assume that $E$ has a rational point of exact order $25$. Let $\mathcal O_{25}$ denote the explicit algebraic obstruction obtained from the order-$25$ Tate-normal-form factorization. Then $$\mathcal O_{25}\text{ holds}.$$ This is the bridge from the abstract torsion hypothesis to the explicit obstruction analyzed by the modular-curve argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_TateOrder25Factor
import Definitions.Def_TorsionDefs

open Polynomial
open scoped WeierstrassCurve.Affine
open MazurProof
open MazurProof.TateOrder25Factor
open MazurProof.TateOriginDivision
open Scratch.TateZ2xZ10Reduction
set_option linter.style.longLine false

theorem MazurProof.TateOrder25Factor.order25_to_explicit_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) :
    ExplicitOrder25Obstruction := by sorry
