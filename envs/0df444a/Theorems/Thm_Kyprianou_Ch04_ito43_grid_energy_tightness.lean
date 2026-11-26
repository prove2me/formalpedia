-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_tightness
-- name    : Kyprianou.Ch04.ito43_grid_energy_tightness
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:52:26.202264+00:00
-- url     : https://prove2.me/theorems/c08d3f16-048a-4250-b32c-8d61df3b5dfa
-- title:
--   Uniform tightness of stopped squared increments for a general Levy process
-- statement:
--   The stopped quadratic grid energy is uniformly bounded in probability on a compact time horizon for any real Levy process, including processes without finite second moments.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Uniform tightness of stopped squared-increment sums for an arbitrary real Levy process. -/

theorem Kyprianou.Ch04.ito43_grid_energy_tightness {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (T : NNReal) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (P {w | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        C ≤ ∑ k ∈ Finset.range n, (X (v (k+1)) w - X (v k) w)^2}).toReal ≤ η := by sorry
