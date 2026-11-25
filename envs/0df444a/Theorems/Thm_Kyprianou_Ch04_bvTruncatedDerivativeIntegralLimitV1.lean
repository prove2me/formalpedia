-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvTruncatedDerivativeIntegralLimitV1
-- name    : Kyprianou.Ch04.bvTruncatedDerivativeIntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:33:03.904369+00:00
-- url     : https://prove2.me/theorems/7b18475e-9ee3-4887-be1a-d0c27fcd3930
-- title:
--   Convergence of the directional derivative time integrals
-- statement:
--   The finite-jump derivative integrability result applies on the half-open interval. Uniform convergence of the derivative integrands implies convergence of their finite-measure integrals. The omitted endpoint has zero measure.
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

theorem Kyprianou.Ch04.bvTruncatedDerivativeIntegralLimitV1
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
    (t : NNReal) (v : ℝ × ℝ) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    Tendsto (fun S => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
      fderiv ℝ f (u,P S (Real.toNNReal u)) v ∂volume) atTop
      (nhds (∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        fderiv ℝ f (u,X (Real.toNNReal u) omega) v ∂volume)) := by
  sorry
