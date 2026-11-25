-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedFderivIntegralLimitV1
-- name    : Kyprianou.Ch04.exercise42LipschitzTruncatedFderivIntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:06:26.585682+00:00
-- url     : https://prove2.me/theorems/5a397491-eb0d-5c7e-a0bb-6ee66661d4bc
-- title:
--   Directional-derivative integral convergence for Lipschitz coordinates under BV truncation
-- statement:
--   Along the same original bounded-variation Lévy process and an arbitrary positive Lipschitz first coordinate, the interval integral of a directional fderiv for finite jump truncations converges to the interval integral for the actual path. The proof is uniform convergence on a compact time interval combined with finite-jump integrability.
-- source:
--   Supporting truncation limit for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineRightCoercionV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpFderivIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedDerivativeUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvUniformSetIntegralLimitV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise42LipschitzTruncatedFderivIntegralLimitV1
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
    Tendsto (fun S => ∫ u in Icc (0 : ℝ) (t : ℝ),
      fderiv ℝ f (U (Real.toNNReal u), P S (Real.toNNReal u)) v ∂volume) atTop
      (nhds (∫ u in Icc (0 : ℝ) (t : ℝ),
        fderiv ℝ f (U (Real.toNNReal u), X (Real.toNNReal u) omega) v ∂volume)) := by
  sorry
