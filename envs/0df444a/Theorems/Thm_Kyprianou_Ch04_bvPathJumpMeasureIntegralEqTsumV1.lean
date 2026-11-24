-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureIntegralEqTsumV1
-- name    : Kyprianou.Ch04.bvPathJumpMeasureIntegralEqTsumV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:12:19.808438+00:00
-- url     : https://prove2.me/theorems/209698f9-ea02-4021-b18e-aa79b8c364f1
-- title:
--   Path jump counting-measure integral equals the absolutely convergent jump series
-- statement:
--   Use the countable set of nonzero jumps on bounded horizons, measurability of cadlag paths and left limits at positive times, the pushforward counting measure, and the local Lipschitz bound to identify the restricted Bochner integral with the actual jump series; zero jumps contribute zero.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.2, p. 91; deterministic pathwise auxiliary obligation.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.bvPathJumpMeasureIntegralEqTsumV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : forall t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) :
    (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            (Set.univ : Set Real),
          (f (z.1, Xleft (Real.toNNReal z.1) omega + z.2) -
           f (z.1, Xleft (Real.toNNReal z.1) omega))
          ∂(pathJumpMeasure X Xleft omega)) =
        (∑' s : Set.Ioc (0 : NNReal) t,
          (f (((s : NNReal) : Real), X s omega) -
            f (((s : NNReal) : Real), Xleft s omega))) := by
  sorry
