-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvTruncatedDerivativeUniformV1
-- name    : Kyprianou.Ch04.bvTruncatedDerivativeUniformV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:33:02.540475+00:00
-- url     : https://prove2.me/theorems/d5f967d9-bd1a-4463-b148-fafd8d78c18b
-- title:
--   Uniform convergence of directional derivative integrands at positive times
-- statement:
--   The derivative within the half-plane is uniformly continuous on the common compact rectangle. Both paths stay in the rectangle and their spatial distance tends uniformly to zero. At positive time the full derivative agrees with the within derivative.
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

theorem Kyprianou.Ch04.bvTruncatedDerivativeUniformV1
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
    TendstoUniformlyOn
      (fun S (u : ℝ) => fderiv ℝ f (u,P S (Real.toNNReal u)) v)
      (fun u : ℝ => fderiv ℝ f (u,X (Real.toNNReal u) omega) v)
      atTop (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  sorry
