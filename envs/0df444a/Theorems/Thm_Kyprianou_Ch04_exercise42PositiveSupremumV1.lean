-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42PositiveSupremumV1
-- name    : Kyprianou.Ch04.exercise42PositiveSupremumV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T17:59:16.98812+00:00
-- url     : https://prove2.me/theorems/32fdd7fc-0516-43c6-948e-c7ab6c151954
-- title:
--   Positive BV drift gives strictly positive running maximum
-- statement:
--   Use the proved almost sure small-time drift limit and the drift-residual monotonicity to find a positive path value before every positive horizon.
-- source:
--   Kyprianou (2006), Exercise 4.2, p. 106 and solution p. 317; deterministic auxiliary or source-law bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42PositiveSupremumV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)

    (hd : 0 < L.drift) :
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
      0 < sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t) := by
  sorry
