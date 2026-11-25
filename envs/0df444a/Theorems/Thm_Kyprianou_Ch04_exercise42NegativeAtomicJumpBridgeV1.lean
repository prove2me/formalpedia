-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42NegativeAtomicJumpBridgeV1
-- name    : Kyprianou.Ch04.exercise42NegativeAtomicJumpBridgeV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:33:06.39953+00:00
-- url     : https://prove2.me/theorems/f195ce20-957d-520d-bc0d-137d689cae1d
-- title:
--   Negative-mark jump integral is the horizon jump series
-- statement:
--   Reuse the proved countable support, atomic counting measure and restricted Dirac integral. Strict negativity of each nonzero mark makes the negative-mark restriction equivalent to the time horizon restriction.
-- source:
--   Kyprianou (2006), Exercise 4.2, p. 106 and solution p. 317; deterministic auxiliary or source-law bridge.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise42NegativeAtomicJumpBridgeV1
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega)
    (hNeg : ∀ t : NNReal, 0 < t → X t omega ≤ Xleft t omega)
    (hSum : ∀ t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|))
    (U : NNReal → Real) (f : Real × Real → Real) (t : NNReal) :
    (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) (Set.Iio (0 : Real)),
      (f (U z.1.toNNReal, Xleft z.1.toNNReal omega + z.2) -
        f (U z.1.toNNReal, Xleft z.1.toNNReal omega))
        ∂(pathJumpMeasure X Xleft omega)) =
      ∑' s : Set.Ioc (0 : NNReal) t,
        (f (U s, X s omega) - f (U s, Xleft s omega)) := by
  sorry
