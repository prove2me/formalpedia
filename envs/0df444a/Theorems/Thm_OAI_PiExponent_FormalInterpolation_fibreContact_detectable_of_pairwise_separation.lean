-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_detectable_of_pairwise_separation
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_detectable_of_pairwise_separation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-22T21:25:53.400276+00:00
-- url     : https://prove2.me/theorems/c619bc82-84a2-475c-91c3-445522789d43
-- title:
--   Weighted derivative detection under ordered separation
-- statement:
--   For positive ordered degree weights W and jet weights V satisfying C times each earlier jet weight is less than every later degree weight, every nonzero polynomial supported below degree N has a nonzero derivative evaluation at a tuple whose coordinates are outside the image of Complex, with derivative cost at most n²N/C.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_detectable_of_pairwise_separation
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
