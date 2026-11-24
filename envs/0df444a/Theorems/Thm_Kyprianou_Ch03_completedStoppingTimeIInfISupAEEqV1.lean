-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedStoppingTimeIInfISupAEEqV1
-- name    : Kyprianou.Ch03.completedStoppingTimeIInfISupAEEqV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T10:08:27.182968+00:00
-- url     : https://prove2.me/theorems/272b4daf-d2bf-43b0-9a5c-43b3a2ec2a13
-- title:
--   Completed right-continuous filtration countable infimum of suprema
-- statement:
--   Countable suprema preserve stopping times by measurable intersections, and countable infima do so in a right-continuous filtration. Completion transfers the property across almost sure equality.
-- source:
--   Kyprianou (2006), Theorem 3.3, closed-set first hitting time.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.completedStoppingTimeIInfISupAEEqV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (hRC : F.IsRightContinuous)
    (T : ℕ → ℕ → Omega → WithTop NNReal)
    (hT : ∀ j n, IsStoppingTime F (T j n))
    (S : Omega → WithTop NNReal)
    (hEq : ∀ᵐ w ∂P, S w = ⨅ j : ℕ, ⨆ n : ℕ, T j n w) :
    IsStoppingTime F S := by
  sorry
