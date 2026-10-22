-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_nonconstant_has_detectable_derivative
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_nonconstant_has_detectable_derivative
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T13:39:23.783581+00:00
-- url     : https://prove2.me/theorems/d065c65c-189c-454f-a3e8-bf4dc4b952f2
-- title:
--   Nonconstant fibre coordinates admit a low-cost derivative witness
-- statement:
--   Assuming every coordinate of x is outside the image of Complex, sufficiently large weighted-support polynomials cannot have all ordinary derivatives through cost sigma N vanish at x: some word of cost at most sigma N has nonzero evaluation.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_nonconstant_has_detectable_derivative
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin m → E) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ∀ F : MvPolynomial (Fin m) Complex, F ≠ 0 →
        fibreContactSupportBound (fun i => w i.succ) N F →
        (∀ word : List (Fin m),
          fibreContactWordCost (fun i => v i.succ) word ≤
            (sigma : Real) * (N : Real) →
          MvPolynomial.aeval x (fibreContactWord word F) = 0) →
        (∀ i : Fin m, ∀ a : Complex,
          x i ≠ algebraMap Complex E a) →
        ∃ word : List (Fin m),
          fibreContactWordCost (fun i => v i.succ) word ≤
            (sigma : Real) * (N : Real) ∧
          MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by sorry
