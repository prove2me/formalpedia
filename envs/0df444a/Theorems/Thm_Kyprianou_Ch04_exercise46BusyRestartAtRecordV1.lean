-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46BusyRestartAtRecordV1
-- name    : Kyprianou.Ch04.exercise46BusyRestartAtRecordV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:33:39.717678+00:00
-- url     : https://prove2.me/theorems/0ca39411-2561-5c99-adbc-5fb69bc5629f
-- title:
--   Canonical busy-start indicator is invariant under restart at a record
-- statement:
--   Translate the left limit and use the proved drawdown restart identity at a running record.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46BusyRestartAtRecordV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (w : Omega) (b u : NNReal) (hu : 0 < u)
    (hrecord : ∀ t ≤ b, L.X t w ≤ L.X b w)
    (hb : BddAbove ((fun t : NNReal => L.X t w) '' Iic (b+u))) :
    let f : NNReal → Real := fun t => L.X t w
    let g : NNReal → Real := fun t => f (b+t) - f b
    (0 < b+u ∧ sSup (f '' Iic (b+u)) = Function.leftLim f (b+u) ∧
      f (b+u) < Function.leftLim f (b+u)) ↔
    (0 < u ∧ sSup (g '' Iic u) = Function.leftLim g u ∧
      g u < Function.leftLim g u) := by
  sorry
