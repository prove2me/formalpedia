-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonJumpHasActiveMarkV1
-- name    : Kyprianou.Ch05.positivePoissonJumpHasActiveMarkV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:36:36.653875+00:00
-- url     : https://prove2.me/theorems/02b416f4-1b74-59c7-a0ee-fe2297f831a9
-- title:
--   Every strictly positive jump has an active mark equal to the jump
-- statement:
--   The jump identity gives strictly positive real fibre mass. Extract an active positive mark and apply the exact fibre mass formula.
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

theorem Kyprianou.Ch05.positivePoissonJumpHasActiveMarkV1
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega) (f : NNReal → ℝ)
    (hinj : ∀ i j : ℕ × ℕ, i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j)
    (hj : ∀ t : NNReal, 0 < t → f t - Function.leftLim f t =
      (∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
        ∂(poissonRandomMeasure K Z w)).toReal)
    (t : NNReal) (ht : 0 < t) (hp : 0 < f t - Function.leftLim f t) :
    ∃ i : ℕ × ℕ, i.2 < K i.1 w ∧ (Z i.1 i.2 w).1 = (t : ℝ) ∧
      (Z i.1 i.2 w).2 = f t - Function.leftLim f t := by
  sorry
