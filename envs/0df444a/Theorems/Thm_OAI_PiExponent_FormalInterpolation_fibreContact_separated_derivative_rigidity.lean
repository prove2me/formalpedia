-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_separated_derivative_rigidity
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_separated_derivative_rigidity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T09:44:41.075894+00:00
-- url     : https://prove2.me/theorems/f84342b2-1926-42f8-bcea-9f515caebeba
-- title:
--   Eventual ordinary derivative rigidity for separated weights
-- statement:
--   For sufficiently large positive N, persistence of all ordinary derivatives through cost sigma N forces a constant coordinate under the exact product-separation inequalities. Prove this using persistent prime components of derivative ideals, weighted normal-basis comparisons, and the separation contradiction. The threshold preserves eventual rectangular-cutoff conditions. This isolates the remaining quantitative algebraic rigidity problem without centers or contact sums.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_separated_derivative_rigidity
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
        ∃ (i : Fin m) (a : Complex), x i = algebraMap Complex E a := by sorry
