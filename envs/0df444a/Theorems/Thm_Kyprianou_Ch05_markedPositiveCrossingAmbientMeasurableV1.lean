-- Prove2me | Theorems.Thm_Kyprianou_Ch05_markedPositiveCrossingAmbientMeasurableV1
-- name    : Kyprianou.Ch05.markedPositiveCrossingAmbientMeasurableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:38:30.017817+00:00
-- url     : https://prove2.me/theorems/215240e9-6f96-40e4-9e90-483adff34155
-- title:
--   Joint ambient measurability of the real-time marked crossing kernel
-- statement:
--   Lift predictable measurability to the ambient product and compose with nonnegative real time conversion. The negative-time kernel is zero.
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

theorem Kyprianou.Ch05.markedPositiveCrossingAmbientMeasurableV1
    {Omega : Type} [MeasurableSpace Omega] (F : Filtration NNReal inferInstance)
    (V : NNReal → Omega → ℝ) (hV : Measurable[F.predictable] (Function.uncurry V))
    (eta x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let psi := fun (s z : ℝ) (w : Omega) =>
      if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
        x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
        x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
    Measurable (fun p : Omega × (ℝ × ℝ) => psi p.2.1 p.2.2 p.1) := by
  sorry
