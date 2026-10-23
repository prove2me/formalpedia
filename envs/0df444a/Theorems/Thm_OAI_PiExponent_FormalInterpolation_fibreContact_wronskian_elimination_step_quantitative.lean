-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_wronskian_elimination_step_quantitative
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_quantitative
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-22T22:39:26.582246+00:00
-- url     : https://prove2.me/theorems/3387d30e-a4c3-4fb0-815f-db854fe240ec
-- title:
--   Quantitative elimination of the last polynomial variable
-- statement:
--   Given quantitative detection for polynomials in the first `n` variables with cost coefficient `B`, this lemma extends detection to `n + 1` variables. It requires positivity of both weight families, a non-image condition for the last coordinate, positive `N`, and the same closed support bound. The added cost allowance is exactly the sum of earlier derivative weights divided by the last support weight.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_quantitative
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
      fibreContactWordCost V word ≤
        (B + (∑ i : Fin n, (V i.castSucc : Real)) /
          (W (Fin.last n) : Real)) * (N : Real) ∧
      MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by sorry
