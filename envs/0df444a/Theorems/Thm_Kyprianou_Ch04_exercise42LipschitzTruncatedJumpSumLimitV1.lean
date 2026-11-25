-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedJumpSumLimitV1
-- name    : Kyprianou.Ch04.exercise42LipschitzTruncatedJumpSumLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:28:58.091151+00:00
-- url     : https://prove2.me/theorems/f0d34dfc-2553-4226-a0bd-980c2c66ad9e
-- title:
--   Dominated convergence of finite-truncation jump ledgers with fixed Lipschitz first coordinate
-- statement:
--   The finite-truncation jump ledger of the test function with fixed first coordinate U converges to the actual infinite jump sum. Compact spatial Lipschitz bounds and the summable jump magnitudes provide domination.
-- source:
--   Supporting truncation limit for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathsUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvCompactSpatialLipschitzV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteTruncationJumpDifferenceV1
import Theorems.Thm_Kyprianou_Ch04_bvContDiffSpatialEvalTendstoV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteSetDominatedSumLimitV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzTruncatedJumpSumLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (omega : Omega) (c : ℝ)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : ℝ) +
        ∑' s : Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (hLeft : ∀ u : NNReal, 0 < u →
      Tendsto (fun v : NNReal => X v omega) (nhdsWithin u (Iio u))
        (nhds (Xleft u omega)))
    (U : NNReal → ℝ) (K : NNReal) (hULip : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (t : NNReal) :
    let j : Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    Tendsto (fun S : Finset (Ioc (0 : NNReal) t) => ∑ s ∈ S,
      (f (U s,P S s) - f (U s,Q S s))) atTop
      (nhds (∑' s : Ioc (0 : NNReal) t,
        (f (U s,X s omega) - f (U s,Xleft s omega)))) := by
  sorry
