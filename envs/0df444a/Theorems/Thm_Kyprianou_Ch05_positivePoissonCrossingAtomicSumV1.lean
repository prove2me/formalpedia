-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonCrossingAtomicSumV1
-- name    : Kyprianou.Ch05.positivePoissonCrossingAtomicSumV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:36:43.615809+00:00
-- url     : https://prove2.me/theorems/2168b15f-ac6f-47bc-8782-9d1bf339def8
-- title:
--   The active mark crossing sum equals the unique path crossing sum
-- statement:
--   Reindex by the positive arrival time. Each marked crossing is a path crossing by the mark-jump identity. Every path crossing has an active mark. The strict passage clock makes the crossing time unique.
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

theorem Kyprianou.Ch05.positivePoissonCrossingAtomicSumV1
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega) (f : NNReal → ℝ)
    (hinj : ∀ i j : ℕ × ℕ, i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j)
    (hj : ∀ t : NNReal, 0 < t → f t - Function.leftLim f t =
      (∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
        ∂(poissonRandomMeasure K Z w)).toReal)
    (hm : Monotone f) (eta x : ℝ) (A B : Set ℝ) :
    (∑' i : ℕ × ℕ, if i.2 < K i.1 w then
      (if 0 < (Z i.1 i.2 w).1 ∧
        Function.leftLim f (Z i.1 i.2 w).1.toNNReal ∈ Icc (0 : ℝ) x ∧
        x - Function.leftLim f (Z i.1 i.2 w).1.toNNReal < (Z i.1 i.2 w).2 ∧
        (Z i.1 i.2 w).2 - (x - Function.leftLim f (Z i.1 i.2 w).1.toNNReal) ∈ A ∧
        x - Function.leftLim f (Z i.1 i.2 w).1.toNNReal ∈ B
        then ENNReal.ofReal (Real.exp (-eta*(Z i.1 i.2 w).1)) else 0) else 0) =
    ∑' t : NNReal, if 0 < t ∧ f t > x ∧ Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
      f t-x ∈ A ∧ x-Function.leftLim f t ∈ B then
      ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  sorry
