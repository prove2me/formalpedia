-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvTruncatedJumpSumLimitV1
-- name    : Kyprianou.Ch04.bvTruncatedJumpSumLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:39:33.946895+00:00
-- url     : https://prove2.me/theorems/d9b44b57-4b01-461d-b29b-ee0da839a167
-- title:
--   Convergence of the finite-jump increments of the test function
-- statement:
--   Use uniform pre/post convergence to get pointwise convergence of each jump increment. The compact spatial mean-value bound controls every truncated increment by a fixed constant times the absolute actual jump. Tannery convergence then gives the finite-set jump series limit.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-subset limit.

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

theorem Kyprianou.Ch04.bvTruncatedJumpSumLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (hLeft : ∀ u : NNReal, 0 < u →
      Tendsto (fun v : NNReal => X v omega) (nhdsWithin u (Set.Iio u))
        (nhds (Xleft u omega)))
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (t : NNReal) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    Tendsto (fun S : Finset (Set.Ioc (0 : NNReal) t) => ∑ s ∈ S,
      (f (((s : NNReal) : ℝ),P S s) - f (((s : NNReal) : ℝ),Q S s))) atTop
      (nhds (∑' s : Set.Ioc (0 : NNReal) t,
        (f (((s : NNReal) : ℝ),X s omega) - f (((s : NNReal) : ℝ),Xleft s omega)))) := by
  sorry
