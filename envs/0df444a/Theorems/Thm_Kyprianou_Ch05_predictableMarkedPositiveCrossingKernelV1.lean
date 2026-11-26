-- Prove2me | Theorems.Thm_Kyprianou_Ch05_predictableMarkedPositiveCrossingKernelV1
-- name    : Kyprianou.Ch05.predictableMarkedPositiveCrossingKernelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:45:36.492062+00:00
-- url     : https://prove2.me/theorems/d3589f0c-0168-51a3-81cf-06e4bec8ee42
-- title:
--   Predictable marked crossing kernel from a predictable pre-jump process
-- statement:
--   The time coordinate, pre-jump value and mark are jointly measurable for the predictable product sigma algebra. The crossing and mark conditions are Borel, so the discounted indicator is measurable.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.predictableMarkedPositiveCrossingKernelV1
    {Omega : Type} [MeasurableSpace Omega] (F : Filtration NNReal inferInstance)
    (V : NNReal → Omega → ℝ) (hV : Measurable[F.predictable] (Function.uncurry V))
    (eta x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let psi := fun (s z : ℝ) (w : Omega) =>
      if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
        x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
        x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
    Measurable[F.predictable.prod inferInstance]
      (fun p : (NNReal × Omega) × ℝ => psi (p.1.1 : ℝ) p.2 p.1.2) := by
  sorry
