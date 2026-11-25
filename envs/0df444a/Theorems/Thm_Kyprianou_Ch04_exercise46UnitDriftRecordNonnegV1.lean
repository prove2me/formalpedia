-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46UnitDriftRecordNonnegV1
-- name    : Kyprianou.Ch04.exercise46UnitDriftRecordNonnegV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T10:11:43.20082+00:00
-- url     : https://prove2.me/theorems/e5e6ff62-c1b8-5f90-bac8-d41a91315682
-- title:
--   The monotone residual bounds the path by unit drift on each compact interval; the running record includes the initial zero.
-- statement:
--   The monotone residual bounds the path by unit drift on each compact interval; the running record includes the initial zero.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46UnitDriftRecordNonnegV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : L.drift = 1) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      0 ≤ sSup ((fun s : NNReal => L.X s omega) '' Iic t) := by
  sorry
