-- Prove2me | Theorems.Thm_Kyprianou_Ch03_monotoneStoppingSupValuesLimitV1
-- name    : Kyprianou.Ch03.monotoneStoppingSupValuesLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:14:03.490803+00:00
-- url     : https://prove2.me/theorems/d4fa7c89-0982-45fe-abee-f274ffd0a623
-- title:
--   Quasi-left-continuity at a finite supremum of increasing stopping times
-- statement:
--   Supremum is a stopping time and increasing clocks converge to it. Apply the proved quasi-left-continuity theorem using finite selectors.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed closed hitting approximation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.monotoneStoppingSupValuesLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (T : ℕ → Omega → WithTop NNReal)
    (hStop : ∀ n, IsStoppingTime F (T n))
    (hMono : ∀ w, Monotone (fun n => T n w)) :
    ∀ᵐ w ∂P, (⨆ n, T n w) ≠ ⊤ →
      Tendsto (fun n => X ((T n w).untopD 0) w) atTop
        (𝓝 (X ((⨆ n, T n w).untopD 0) w)) := by
  sorry
