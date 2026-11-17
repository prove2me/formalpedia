-- Prove2me | Theorems.Thm_MazurProof_TateOriginDivision_exists_tate_parameters_of_has_rational_point_of_odd_order
-- name    : MazurProof.TateOriginDivision.exists_tate_parameters_of_has_rational_point_of_odd_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:49.941298+00:00
-- url     : https://prove2.me/theorems/62661fc9-32e9-4184-a4b9-221f5c8026ac
-- title:
--   Odd rational torsion yields Tate parameters and a vanishing division polynomial
-- statement:
--   Let $E/ℚ$ be an elliptic curve, let $n>3$ be odd, and assume $E$ has a rational point of exact order $n$. Then there exist $b,c∈ℚ$ such that $W(b,c)$ is elliptic, its distinguished Tate origin has exact order $n$, $b≠0$, and $$\operatorname{preΨ}'_n(0)=0.$$ This translates odd rational torsion into explicit Tate-normal-form equations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_TateOriginDivision
import Definitions.Def_TorsionDefs

open Polynomial
open scoped WeierstrassCurve.Affine
open MazurProof
open MazurProof.TateOriginDivision
open Scratch.TateZ2xZ10Reduction

theorem MazurProof.TateOriginDivision.exists_tate_parameters_of_has_rational_point_of_odd_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn3 : 3 < n) (hnodd : ¬ Even n)
    (hP : HasRationalPointOfOrder E n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          ((W b c).preΨ' n).eval 0 = 0 := by sorry
