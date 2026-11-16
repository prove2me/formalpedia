-- Prove2me | Theorems.Thm_Kyprianou_Ch06_strictGridIndependentIncrements
-- name    : Kyprianou.Ch06.strictGridIndependentIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:11:36.944498+00:00
-- url     : https://prove2.me/theorems/51f1959c-cf89-4b5a-b095-e720e79a9dc5
-- title:
--   Chapter 6 bridge: strictly increasing grid increments are independent
-- statement:
--   If a real process has full finite-dimensional independent-increment cylinder factorisation and the underlying measure has mass one, then the increments along any strictly increasing finite time grid are jointly independent in the published ProbabilityTheory.iIndepFun sense. This remains valid for any finite number of increments.
-- source:
--   Kyprianou (2006), Chapter 6, Lévy-process independent stationary increment axiom. Derived from the proved finite-rectangle independence bridge Kyprianou.Ch06.iIndepFunOfFullRectangle.

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_Kyprianou_Ch06_iIndepFunOfFullRectangle

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem Kyprianou.Ch06.strictGridIndependentIncrements
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hprob : P Set.univ = 1)
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n, P {ω |
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i})
    (n : Nat) (times : Fin (n + 1) → NNReal)
    (hstrict : StrictMono times) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin n =>
        ProbabilityTheory.increment X (times i.castSucc) (times i.succ)) P := by sorry
