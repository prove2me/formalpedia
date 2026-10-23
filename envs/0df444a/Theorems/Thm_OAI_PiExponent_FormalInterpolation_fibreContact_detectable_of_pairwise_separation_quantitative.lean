-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_detectable_of_pairwise_separation_quantitative
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_detectable_of_pairwise_separation_quantitative
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-22T21:41:38.431045+00:00
-- url     : https://prove2.me/theorems/b12eb202-946a-45db-bd89-b230d0706eb4
-- title:
--   Quantitative weighted derivative detection under ordered separation
-- statement:
--   For positive degree and jet weights with strict ordered separation, a nonzero polynomial supported within degree N has a derivative word whose evaluation is nonzero at a tuple whose coordinates are outside the image of Complex. The word cost is at most n²N/C, retaining all support, positivity, separation, and range hypotheses.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_detectable_of_pairwise_separation_quantitative
    {n : Nat} (C : Real) (hC : 0 < C)
    (W V : Fin n → Rat)
    (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
    (hsep : ∀ i j : Fin n, i < j → C * (V i : Real) < (W j : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin n → E)
    (hx : ∀ i : Fin n, ∀ a : Complex, x i ≠ algebraMap Complex E a)
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin n) Complex) (hF : F ≠ 0)
    (hbound : fibreContactSupportBound W N F) :
    ∃ word : List (Fin n),
      fibreContactWordCost V word ≤ ((n : Real) ^ 2 / C) * (N : Real) ∧
      MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by sorry
