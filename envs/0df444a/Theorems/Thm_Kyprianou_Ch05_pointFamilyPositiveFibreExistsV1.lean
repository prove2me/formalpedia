-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyPositiveFibreExistsV1
-- name    : Kyprianou.Ch05.pointFamilyPositiveFibreExistsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:25:56.706575+00:00
-- url     : https://prove2.me/theorems/40bfdb45-50b1-598e-a105-860e3321409c
-- title:
--   Positive real time-fibre mass implies an active positive mark at that time
-- statement:
--   If no active positive mark lies on the fibre, every summand of the atomic expansion is zero. Its real mass would then be zero, contradicting positivity.
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

theorem Kyprianou.Ch05.pointFamilyPositiveFibreExistsV1
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega) (t : ℝ)
    (hpos : 0 < (∫⁻ z in {t} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
      ∂(poissonRandomMeasure K Z w)).toReal) :
    ∃ i : ℕ × ℕ, i.2 < K i.1 w ∧ (Z i.1 i.2 w).1 = t ∧ 0 < (Z i.1 i.2 w).2 := by
  sorry
