-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteVectorLawOfPrefixRectanglesV1
-- name    : Kyprianou.Ch03.strongMarkovFiniteVectorLawOfPrefixRectanglesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T08:20:17.12302+00:00
-- url     : https://prove2.me/theorems/4e42c1f8-3fc9-4f57-b4b6-255b1448687a
-- title:
--   Finite vector law from restricted prefix rectangles
-- statement:
--   Extend each finite cylinder by unrestricted coordinates and apply finite-cylinder uniqueness.
-- source:
--   Kyprianou (2006), Theorem 3.1; ordered increment law 5b897d7e-28a6-462c-8017-67231f6a80df.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovFiniteVectorLawOfPrefixRectanglesV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P] (A : Set Omega) (n : ℕ)
    (U V : Omega → (Fin n → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (hRect : ∀ C : ℕ → Set ℝ, (∀ k, MeasurableSet (C k)) →
      P (A ∩ {w | ∀ k : ℕ, ∀ hk : k < n, U w ⟨k,hk⟩ ∈ C k}) =
        P A * P {w | ∀ k : ℕ, ∀ hk : k < n, V w ⟨k,hk⟩ ∈ C k}) :
    Measure.map U (P.restrict A) = P A • Measure.map V P := by
  sorry
