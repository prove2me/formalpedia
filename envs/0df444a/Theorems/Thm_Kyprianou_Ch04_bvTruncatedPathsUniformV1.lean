-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathsUniformV1
-- name    : Kyprianou.Ch04.bvTruncatedPathsUniformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:28:29.285249+00:00
-- url     : https://prove2.me/theorems/c8c8df22-e6df-4c17-a3af-72855e4da59a
-- title:
--   Uniform convergence of right and left finite-jump truncations
-- statement:
--   The omitted absolute tail tends to zero along the directed finite subsets. The two pathwise tail inequalities imply uniform convergence on their respective horizons.
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

theorem Kyprianou.Ch04.bvTruncatedPathsUniformV1
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
    TendstoUniformlyOn P (fun u => X u omega) atTop (Set.Icc 0 t) ∧
      TendstoUniformlyOn Q (fun u => Xleft u omega) atTop (Set.Ioc 0 t) := by
  sorry
