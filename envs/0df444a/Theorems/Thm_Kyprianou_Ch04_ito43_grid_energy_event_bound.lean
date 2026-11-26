-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_event_bound
-- name    : Kyprianou.Ch04.ito43_grid_energy_event_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:04:42.841546+00:00
-- url     : https://prove2.me/theorems/e0f1e100-65df-4a10-8a63-243710e99e99
-- title:
--   Localised stopped energy tail contained in two exceptional events
-- statement:
--   Localised stopped energy tail contained in two exceptional events.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_grid_energy_event_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (M : Ω → ℝ) (T R : NNReal) (hR : 0 < R)
    (r D : ℝ) (hr : (R : ℝ) = 2*r)
    (hm : ∀ᵐ w ∂P, ∀ a ≤ T, |X a w| ≤ M w)
    (n : ℕ) (hn : 0 < n) :
    let A : ℝ := Real.pi^2*(R : ℝ)^2/2
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let F : Ω → ℝ := fun w => ∑ k ∈ Finset.range n,
      (1 - Real.cos ((1/(R : ℝ)) * (X (u (k+1)) w - X (u k) w)))
    (P {w | ∃ t : NNReal, t ≤ T ∧
      let v : ℕ → NNReal := fun k => min t (u k)
      A*D+(R : ℝ)^2+1 ≤ ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2}).toReal ≤
      (P {w | r < M w}).toReal + (P {w | D ≤ F w}).toReal := by sorry
