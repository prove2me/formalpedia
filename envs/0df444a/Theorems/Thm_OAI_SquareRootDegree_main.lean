-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_main
-- name    : OAI.SquareRootDegree.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:25.816251+00:00
-- url     : https://prove2.me/theorems/def3ded1-5e48-43e5-916a-3ea8409ae4d7
-- statement:
--   The theorem, currently admitted without proof, states two things about real Fourier analysis on Boolean cubes, where a Boolean input is read as a sign (false is +1, true is -1), averages are uniform, and degree is the ordinary real Fourier degree, meaning the largest size of a subset s with nonzero Fourier coefficient, the coefficient being the average of f(x) times the product of the signs of the coordinates in s. First, SignedViolations holds: for every real C>0 there is a positive integer n and a function f from {false,true}^n to the reals that takes only the values -1 and 1, is nonconstant, and satisfies C·√(deg f) < Σᵢ f̂({i}), the plain signed sum of its degree-one Fourier coefficients over single coordinates. Second, the set of ratios (Σᵢ |f̂({i})|)/√(deg f), taken over all positive n and all Boolean-valued f on n coordinates with positive Fourier degree, is not bounded above in the reals, so the supremum of these ratios is infinite.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SquareRootDegree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SquareRootDegree.lean; bytes 1677..1907
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SquareRootDegree

namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-- The two clauses of the literal main theorem. Unboundedness above is the
real-valued formulation of the displayed supremum being positive infinity. -/
theorem main : SignedViolations ∧ ¬ BddAbove AbsoluteRatios := by
  sorry

end SquareRootDegree
end
end OAI
