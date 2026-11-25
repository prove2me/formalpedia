-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42AvramPathDataV1
-- name    : Kyprianou.Ch04.exercise42AvramPathDataV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T08:22:44.888582+00:00
-- url     : https://prove2.me/theorems/77540500-4b36-543f-bc0a-71091a70a697
-- title:
--   Actual BV source path data for Exercise 4.2
-- statement:
--   On the same full event combine actual BV drift-jump representation, cadlag paths, spectral negativity, positive small-time drift and monotonicity of the drift residual.
-- source:
--   Kyprianou (2006), Exercise 4.2, p. 106 and solution p. 317; deterministic and source-law reduction.

import Mathlib
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

theorem Kyprianou.Ch04.exercise42AvramPathDataV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => L.X s omega)
          (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega))) :
    ∀ᵐ omega : Omega ∂P,
      IsCadlag (fun t : NNReal => L.X t omega) ∧
      (∀ t : NNReal, 0 < t →
        Tendsto (fun s : NNReal => L.X s omega)
          (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega))) ∧
      (∀ t : NNReal, 0 < t → L.X t omega ≤ Xleft t omega) ∧
      (∀ t : NNReal,
        Summable (fun s : Set.Ioc (0 : NNReal) t => |L.X s omega - Xleft s omega|) ∧
        L.X t omega = L.X 0 omega + L.drift * (t : Real) +
          ∑' s : Set.Ioc (0 : NNReal) t, (L.X s omega - Xleft s omega)) ∧
      (∀ t : NNReal, 0 < t →
        0 < sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) ∧
      Monotone (fun t : NNReal => (t : Real) * L.drift - L.X t omega) := by
  sorry
