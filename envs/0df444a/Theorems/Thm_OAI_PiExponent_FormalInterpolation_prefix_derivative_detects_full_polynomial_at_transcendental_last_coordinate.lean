-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_prefix_derivative_detects_full_polynomial_at_transcendental_last_coordinate
-- name    : OAI.PiExponent.FormalInterpolation.prefix_derivative_detects_full_polynomial_at_transcendental_last_coordinate
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-22T23:23:35.598358+00:00
-- url     : https://prove2.me/theorems/a3600333-4757-4498-98c4-85aa631ea96e
-- title:
--   Prefix derivatives detect a polynomial with a transcendental last coordinate
-- statement:
--   Under the prefix detection hypothesis, a nonzero polynomial with the given closed support bound has a prefix-only derivative word, with cost at most B times N, whose evaluation at x is nonzero when the last coordinate lies outside the image of Complex.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.prefix_derivative_detects_full_polynomial_at_transcendental_last_coordinate
    {n : Nat} (W V : Fin (n + 1) → Rat)
    (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin (n + 1) → E)
    (hlast : ∀ a : Complex, x (Fin.last n) ≠ algebraMap Complex E a)
    (B : Real)
    (hprefix : ∀ T : Nat, 0 < T →
      ∀ U : MvPolynomial (Fin n) Complex, U ≠ 0 →
        fibreContactSupportBound (fun i => W i.castSucc) T U →
        ∃ word : List (Fin n),
          fibreContactWordCost (fun i => V i.castSucc) word ≤ B * (T : Real) ∧
          MvPolynomial.aeval (fun i => x i.castSucc) (fibreContactWord word U) ≠ 0)
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin (n + 1)) Complex) (hF : F ≠ 0)
    (hbound : fibreContactSupportBound W N F) :
    ∃ word : List (Fin (n + 1)),
      (∀ i ∈ word, ∃ j : Fin n, i = j.castSucc) ∧
      fibreContactWordCost V word ≤ B * (N : Real) ∧
      MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by sorry
