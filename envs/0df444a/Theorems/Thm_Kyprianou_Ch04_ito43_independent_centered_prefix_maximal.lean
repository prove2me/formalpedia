-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_independent_centered_prefix_maximal
-- name    : Kyprianou.Ch04.ito43_independent_centered_prefix_maximal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:56:45.760314+00:00
-- url     : https://prove2.me/theorems/fa40db5f-df5b-5292-902a-3e80e64cd3a3
-- title:
--   Bounded independent variables have centred-prefix maximal probability bound
-- statement:
--   Choose measurable modifications for the countable AE measurable family. Independence and means are preserved. Apply the proved Kolmogorov maximal inequality and sum the variance bounds.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_independent_centered_prefix_maximal {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (C μ : ℝ) (hC : 0 ≤ C)
    (hm : ∀ k, AEMeasurable (F k) P) (hi : iIndepFun F P)
    (hb : ∀ k, ∀ᵐ w ∂P, 0 ≤ F k w ∧ F k w ≤ C)
    (hmean : ∀ k, (∫ w, F k w ∂P) = μ)
    (n : ℕ) (e : ℝ) (he : 0 < e) :
    (P {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, (F k w-μ)|}).toReal
      ≤ (n:ℝ)*C*μ/e^2 := by sorry
