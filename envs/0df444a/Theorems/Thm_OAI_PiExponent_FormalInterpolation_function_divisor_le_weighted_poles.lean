-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_function_divisor_le_weighted_poles
-- name    : OAI.PiExponent.FormalInterpolation.function_divisor_le_weighted_poles
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T23:09:36.812568+00:00
-- url     : https://prove2.me/theorems/8d18293b-1e87-4bc3-b23c-bb57f0fb588f
-- title:
--   Bound a coordinate zero divisor by weighted curve poles
-- statement:
--   This child removes the function-field product formula and weighted pole comparison. Transcendence makes f=xₖ−b nonzero. An independent proof realizes E as a finite extension of Complex(xₖ), identifies the normalized additive valuations with places of its smooth projective curve, and establishes finite divisor support and degree zero for the principal divisor of f. Residue degrees are one because Complex is algebraically closed. Hence total positive order equals total pole order. Subtracting a constant preserves every negative order, so f and xₖ have the same pole divisor. At each place, the supremum defining polynomialCurvePole dominates −ord(xₖ)/wₖ; its additional zero entry handles nonpole places. Positive wₖ permits multiplication, and finite support permits summation. The remaining core obligation is formalizing the divisor theorem for PolynomialCurvePlace and connecting it to finsum. All weights remain strictly positive; d=0 is excluded by the parameter k : Fin d. This standard divisor argument is proposed for the current definitions, not claimed as an existing formal proof.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.function_divisor_le_weighted_poles
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (k : Fin d) (hk : Transcendental Complex (x k)) (b : Complex) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu
        (x k - algebraMap Complex E b) : Real) 0) ≤
      (w k : Real) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by sorry
