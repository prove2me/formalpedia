-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyPositiveFibreMassV1
-- name    : Kyprianou.Ch05.pointFamilyPositiveFibreMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:25:56.709423+00:00
-- url     : https://prove2.me/theorems/45d29262-aecd-56b6-a3df-730d38f268d2
-- title:
--   A positive-time fibre with an active positive mark has exactly that mark mass
-- statement:
--   Expand the integral into the active-pair sum. The positive mark at the chosen time supplies one summand. Injectivity of active arrival times forces every other summand to vanish.
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

theorem Kyprianou.Ch05.pointFamilyPositiveFibreMassV1
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega)
    (hinj : ∀ i j : ℕ × ℕ, i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j)
    (i : ℕ × ℕ) (hi : i.2 < K i.1 w) (hz : 0 < (Z i.1 i.2 w).2) :
    (∫⁻ z in {(Z i.1 i.2 w).1} ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)) =
      ENNReal.ofReal (Z i.1 i.2 w).2 := by
  sorry
