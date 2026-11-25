-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvRightTruncationTailBoundV1
-- name    : Kyprianou.Ch04.bvRightTruncationTailBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:28:17.131799+00:00
-- url     : https://prove2.me/theorems/d583fe7d-e466-4ff6-a408-889b1deaeb36
-- title:
--   Uniform right-path truncation error on a compact horizon
-- statement:
--   Reindex the actual path formula to the fixed horizon, cancel the initial value and drift, and apply the dominated tail estimate.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic absolutely summable jump approximation.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.bvRightTruncationTailBoundV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (t : NNReal) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    ∀ (S : Finset (Set.Ioc (0 : NNReal) t)) (u : NNReal), u ≤ t →
      |X u omega - P S u| ≤ (∑' s, |j s|) - ∑ s ∈ S, |j s| := by
  sorry
