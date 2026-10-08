-- Prove2me | Theorems.Thm_MazurTransfer_order18_minimal_point_halving_of_square_difference
-- name    : MazurTransfer.order18_minimal_point_halving_of_square_difference
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T16:44:47.000328+00:00
-- url     : https://prove2.me/theorems/9941087d-acce-4e04-b196-8ad10424ceff
-- title:
--   Order18: a square difference in the compositum supplies a rational half
-- statement:
--   Let \(K\), \(M\), the completed-square model \(E/K\), and its explicit cubic root \(\eta\in M\) be the published minimal descent data. For a nonsingular affine point \(P=(x,y)\in E(K)\), if \(x-\eta\) is a square in \(M\), then \[\exists Q\in E(K),\qquad 2Q=P.\] The square condition is the explicit hypothesis of this intermediate halving criterion. The unconditional order-18 descent supplies this condition separately.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, original Apache-2.0 headers and attribution retained. The original generic two-descent halving and minimal algebra-equivalence closures is selected from typed kernel dependencies and complete original Lean AST declaration ranges. Pure minimal model and cubic-root data is published separately. All imported rational/relative field and arithmetic interfaces are actually Proved. This is a genuinely smaller arithmetic subproblem after retained 13604-line and 11373-line descent verification timeouts. Named downstream consumer: MazurTransfer.order18_original_quotient_doubling_surjective and the unchanged full rational genus-two campaign exclusion. No custom axioms, proof-strengthening options or new final hypotheses.

import Mathlib
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData

theorem MazurTransfer.order18_minimal_point_halving_of_square_difference (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentCurve.toAffine.Nonsingular x y)
    (hsq : IsSquare (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM)) :
    ∃ Q : MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentCurve.toAffine.Point,
      2 • Q = .some x y h := by sorry
