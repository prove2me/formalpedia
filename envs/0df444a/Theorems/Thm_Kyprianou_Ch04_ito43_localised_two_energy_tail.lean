-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_localised_two_energy_tail
-- name    : Kyprianou.Ch04.ito43_localised_two_energy_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:29:27.603531+00:00
-- url     : https://prove2.me/theorems/6ec94f01-7f69-5dd2-a5cb-d856c05405f1
-- title:
--   Uniform outer-probability error tail from two localised energy bounds
-- statement:
--   Combine two exceptional localisation events and the grid-energy tail to bound the uniform error in outer probability.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A uniform error bounded by two localised energies has a small outer-probability tail. -/

theorem Kyprianou.Ch04.ito43_localised_two_energy_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : NNReal) (U V : Set Ω) (Q E : ℕ → NNReal → Ω → ℝ) (J : Ω → ℝ)
    (C D a e eta : ℝ) (ha : 0 ≤ a) (hsmall : a*(C+D) < e)
    (hU : (P U).toReal ≤ eta/3) (hV : (P V).toReal ≤ eta/3)
    (hQ : ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, C ≤ Q n t w}).toReal ≤ eta/3)
    (hgood : ∀ᵐ w ∂P, w ∉ U → w ∉ V →
      J w ≤ D ∧ ∀ n t, t ≤ T → |E n t w| ≤ a*(Q n t w+J w)) :
    ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal ≤ eta := by sorry
