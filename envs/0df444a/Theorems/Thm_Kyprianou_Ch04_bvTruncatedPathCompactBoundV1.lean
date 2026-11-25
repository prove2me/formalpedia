-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
-- name    : Kyprianou.Ch04.bvTruncatedPathCompactBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:32:03.295494+00:00
-- url     : https://prove2.me/theorems/bd9fe417-4c17-48e8-87a6-737854c48835
-- title:
--   Common compact spatial interval for actual and truncated paths
-- statement:
--   Bound both finite approximations by the same absolute jump sum radius, then pass the inequalities to the uniform limits.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

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

theorem Kyprianou.Ch04.bvTruncatedPathCompactBoundV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (hLeft : ∀ u : NNReal, 0 < u →
      Tendsto (fun v : NNReal => X v omega) (nhdsWithin u (Set.Iio u))
        (nhds (Xleft u omega)))
    (t : NNReal) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    let M := |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
    0 ≤ M ∧
      (∀ S u, u ≤ t → |P S u| ≤ M ∧ |Q S u| ≤ M) ∧
      (∀ u, u ≤ t → |X u omega| ≤ M) ∧
      (∀ u, 0 < u → u ≤ t → |Xleft u omega| ≤ M) := by
  sorry
