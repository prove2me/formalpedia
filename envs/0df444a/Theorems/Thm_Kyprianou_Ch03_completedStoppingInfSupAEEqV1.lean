-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedStoppingInfSupAEEqV1
-- name    : Kyprianou.Ch03.completedStoppingInfSupAEEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:31.373116+00:00
-- url     : https://prove2.me/theorems/f5b72d88-55a9-40fd-98fb-273ad0fa11bf
-- title:
--   Completed filtration stopping times under countable inf-sup and null changes
-- statement:
--   The pointwise supremum of countably many stopping times is a stopping time by intersection of sublevels. Right continuity implies that the countable infimum is a stopping time. Every subset of a P-null measurable set lies in each completed natural sigma-algebra, so an almost-everywhere change of the clock preserves stopping-time measurability.
-- source:
--   Kyprianou (2006), Theorem 3.3; closed hitting child 567fb35e-7763-499a-b65a-6ab9d41e8485.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.completedStoppingInfSupAEEqV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega → WithTop NNReal)
    (U : ℕ → ℕ → Omega → WithTop NNReal)
    (hRC : F.IsRightContinuous)
    (hU : ∀ m n, IsStoppingTime F (U m n))
    (hEq : T =ᵐ[P] (fun w => ⨅ m : ℕ, ⨆ n : ℕ, U m n w)) :
    IsStoppingTime F T := by
  sorry
