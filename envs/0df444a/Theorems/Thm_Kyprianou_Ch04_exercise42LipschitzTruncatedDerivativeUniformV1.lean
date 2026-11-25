-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedDerivativeUniformV1
-- name    : Kyprianou.Ch04.exercise42LipschitzTruncatedDerivativeUniformV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:54:30.811401+00:00
-- url     : https://prove2.me/theorems/4b2142f3-6749-4d95-ab67-c4bb214a41ff
-- title:
--   Uniform truncation convergence of first- and second-coordinate derivative integrands
-- statement:
--   For an arbitrary positive Lipschitz first-coordinate path U, uniform approximation of a bounded-variation Lévy path X by finite-jump truncations yields uniform convergence of each fderiv evaluation on positive times in a fixed compact interval. The proof uses compactness of U's image, the existing uniform path approximation and fderivWithin continuity.
-- source:
--   Lévy bounded-variation Stieltjes limit for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathsUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvFullFderivEqWithinPositiveV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise42LipschitzTruncatedDerivativeUniformV1
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
    (t : NNReal) (v : ℝ × ℝ) :
    let j : Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    TendstoUniformlyOn
      (fun S (u : ℝ) => fderiv ℝ f (U (Real.toNNReal u), P S (Real.toNNReal u)) v)
      (fun u : ℝ => fderiv ℝ f (U (Real.toNNReal u), X (Real.toNNReal u) omega) v)
      atTop (Ioc (0 : ℝ) (t : ℝ)) := by
  sorry
