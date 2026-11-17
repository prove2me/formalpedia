-- Prove2me | Theorems.Thm_MazurProof_TateOriginDivision_prePsi_eval_ne_zero_of_lt_addOrder
-- name    : MazurProof.TateOriginDivision.prePsi_eval_ne_zero_of_lt_addOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:05:03.565373+00:00
-- url     : https://prove2.me/theorems/076e8985-b732-47d3-a5b1-8a7bbe4a502f
-- title:
--   Odd lower division polynomials do not vanish before the exact order
-- statement:
--   Let $W(b,c)$ be an elliptic Tate normal-form curve over $ℚ$, let its distinguished origin point have exact additive order $n$, and let $m$ satisfy $0<m<n$ and be odd. Then the modified division polynomial satisfies $$\operatorname{preΨ}'_m(0)≠0.$$ This isolates the first possible odd division-polynomial vanishing at the exact torsion order.
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

theorem MazurProof.TateOriginDivision.prePsi_eval_ne_zero_of_lt_addOrder
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {m n : ℕ} (hnpos : 0 < n) (hmpos : 0 < m) (hmn : m < n)
    (hmodd : ¬ Even m) (hord : addOrderOf (tateOrigin b c) = n) :
    ((W b c).preΨ' m).eval 0 ≠ 0 := by sorry
