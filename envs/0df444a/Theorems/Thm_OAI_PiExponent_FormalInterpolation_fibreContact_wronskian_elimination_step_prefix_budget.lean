-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_wronskian_elimination_step_prefix_budget
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_prefix_budget
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T03:43:13.547246+00:00
-- url     : https://prove2.me/theorems/46616e85-8bfd-4f17-afef-ec5b9d9e1abb
-- title:
--   Prefix budget detects the leading last-coordinate coefficient
-- statement:
--   Under the parent hypotheses, a prefix derivative word of cost at most B times N makes the evaluation of F nonzero. A proof can select the highest nonzero coefficient in the last variable, detect that coefficient using hprefix, then use transcendence of the last coordinate to show the resulting polynomial does not vanish.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_prefix_budget
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
      fibreContactWordCost V word ≤ B * (N : Real) ∧
      MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by sorry
