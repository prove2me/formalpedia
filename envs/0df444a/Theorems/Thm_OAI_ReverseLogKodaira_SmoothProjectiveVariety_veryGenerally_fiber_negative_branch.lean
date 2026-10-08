-- Prove2me | Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_veryGenerally_fiber_negative_branch
-- name    : OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:16.280289+00:00
-- url     : https://prove2.me/theorems/73c8a3cb-3317-4759-bec4-be0d32078398
-- statement:
--   The theorem states that, for smooth projective complex varieties X and Y, each equipped with a reduced simple-normal-crossing boundary (E on X, D on Y, given by Cartier components with transverse intersections and Cartier union), and for a stratum-smooth fibration f from (X,E) to (Y,D), the following holds for very general points of Y. Here f is a surjective morphism over ℂ with connected fibers over complex points, whose preimage of the support of D lies in the support of E, and which is smooth over the complement of D both on X and on every stratum, meaning each intersection of a nonempty set of components of E. Very general means there is a countable family of proper closed subsets Zₙ of Y such that every complex point y of Y outside all the Zₙ satisfies the property. The property is that y lies in the complement of D and, for every fiber model F of f over y whose boundary has log Kodaira dimension equal to ⊥ (the value meaning there is no nonzero log pluriform section of any positive degree m on the fiber), the log Kodaira dimension of E equals that of D plus that of the fiber boundary F.boundary, and moreover every log m-pluriform rational section of X with poles allowed along E, for every integer m>0, is zero. A fiber model is a smooth projective variety mapping to X as the fiber product of f with the point y, together with an SNC boundary whose ideal is the pullback of E's ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LogKodairaFiberNegative.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LogKodairaFiberNegative.lean; bytes 9344..9817
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_LogKodairaFiberNegative

namespace OAI

noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped TensorProduct

namespace ReverseLogKodaira.SmoothProjectiveVariety

theorem veryGenerally_fiber_negative_branch
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) :
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      ∀ F : FiberModel f.toBoundaryFibration y, F.boundary.kodaira = ⊥ →
        E.kodaira = D.kodaira + F.boundary.kodaira ∧
        ∀ (m : ℕ), 0 < m → ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by sorry

end ReverseLogKodaira.SmoothProjectiveVariety
end
end OAI
