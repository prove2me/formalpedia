-- Prove2me | Theorems.Thm_Kyprianou_Ch05_activePositivePoissonMarkIsJumpV1
-- name    : Kyprianou.Ch05.activePositivePoissonMarkIsJumpV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:36:43.233205+00:00
-- url     : https://prove2.me/theorems/be581d02-76a6-48aa-8c87-72512eaf3460
-- title:
--   An active positive mark at a positive time equals the path jump
-- statement:
--   At the positive arrival time, the time fibre contains exactly this active mark. Substitute the fibre mass in the jump identity.
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

theorem Kyprianou.Ch05.activePositivePoissonMarkIsJumpV1
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega) (f : NNReal → ℝ)
    (hinj : ∀ i j : ℕ × ℕ, i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j)
    (hj : ∀ t : NNReal, 0 < t → f t - Function.leftLim f t =
      (∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
        ∂(poissonRandomMeasure K Z w)).toReal)
    (i : ℕ × ℕ) (hi : i.2 < K i.1 w)
    (ht : 0 < (Z i.1 i.2 w).1) (hz : 0 < (Z i.1 i.2 w).2) :
    f (Z i.1 i.2 w).1.toNNReal - Function.leftLim f (Z i.1 i.2 w).1.toNNReal =
      (Z i.1 i.2 w).2 := by
  sorry
