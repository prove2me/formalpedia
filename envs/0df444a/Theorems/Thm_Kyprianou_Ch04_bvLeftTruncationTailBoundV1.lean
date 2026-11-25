-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvLeftTruncationTailBoundV1
-- name    : Kyprianou.Ch04.bvLeftTruncationTailBoundV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:28:26.744383+00:00
-- url     : https://prove2.me/theorems/95b9347e-dc7f-4ca4-b36b-98bdffa3d841
-- title:
--   Uniform left-path truncation error on a compact horizon
-- statement:
--   Pass the uniform right-path error estimate to the left limit at each positive time. The finite path has the explicit strict-before left limit.
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

theorem Kyprianou.Ch04.bvLeftTruncationTailBoundV1
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
    let Q : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    ∀ (S : Finset (Set.Ioc (0 : NNReal) t)) (u : NNReal), 0 < u → u ≤ t →
      |Xleft u omega - Q S u| ≤ (∑' s, |j s|) - ∑ s ∈ S, |j s| := by
  sorry
