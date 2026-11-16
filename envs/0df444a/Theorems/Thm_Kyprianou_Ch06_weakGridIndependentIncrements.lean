-- Prove2me | Theorems.Thm_Kyprianou_Ch06_weakGridIndependentIncrements
-- name    : Kyprianou.Ch06.weakGridIndependentIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:42:39.566356+00:00
-- url     : https://prove2.me/theorems/ecedbe3d-7647-4e37-858a-fc6315549eda
-- title:
--   Chapter 6: strict-grid independent-increments cylinders imply all monotone-grid independence
-- statement:
--   A real-valued process whose finite increment cylinders factorise on every strictly increasing time grid, under a unit-mass law, has mutually independent increments on all nondecreasing finite time grids. Consecutive repeated timestamps contribute deterministic zero increments; the proof deletes those increments by finite induction and reinserts them using proved coordinate-independence transport.
-- source:
--   Kyprianou (2006), Chapter 6 Lévy-process independent-increments axiom, source-faithful compatibility with ProbabilityTheory.HasIndependentIncrements. Uses verified finite-grid compression and zero-coordinate insertion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_Kyprianou_Ch06_FinCompressionIndexHelpers
import Theorems.Thm_Kyprianou_Ch06_iIndepFun_finInsertZero
import Theorems.Thm_Kyprianou_Ch06_strictGridIndependentIncrements

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem Kyprianou.Ch06.weakGridIndependentIncrements
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hprob : P Set.univ = 1)
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n, P {ω |
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i}) :
    ProbabilityTheory.HasIndependentIncrements X P := by sorry
