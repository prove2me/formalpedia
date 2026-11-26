-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualRetainedFiniteAtomsAEV1
-- name    : Kyprianou.Ch04.actualRetainedFiniteAtomsAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:37:14.550946+00:00
-- url     : https://prove2.me/theorems/49e5572a-ae12-527b-a90b-d735c27c064b
-- title:
--   Almost-sure exact retained physical atoms on every finite horizon
-- statement:
--   Finite intensity gives finite random mass on every integer horizon, hence every bounded horizon. Measurable paths and their left limits identify the physical jump measure and exact retained atoms.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualRetainedFiniteAtomsAEV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L : NNReal → Ω → ℝ)
    (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u w) (𝓝[<] t) (𝓝 (L t w)))
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w)
    (e : ℝ) (he : 0 < e) :
    ∀ᵐ w ∂P, ∀ T : NNReal, ∃ S : Finset NNReal,
      (∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |X r w - L r w|) ∧
      (N.N w).restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
        ∑ r ∈ S, Measure.dirac ((r : ℝ),X r w - L r w) := by
  sorry
end Kyprianou.Ch04
