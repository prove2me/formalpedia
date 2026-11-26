-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ZeroVisitsLocallyFiniteV1
-- name    : Kyprianou.Ch04.exercise41ZeroVisitsLocallyFiniteV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:03:29.500833+00:00
-- url     : https://prove2.me/theorems/8cd476ba-fd14-5bf6-a617-1b1f1b6936ac
-- title:
--   Spectrally negative positive-drift BV Lévy process has locally finite zero visits
-- statement:
--   For the actual sample-path process of a spectrally negative bounded-variation Lévy process with strictly positive drift on its original probability space, almost surely the strictly positive zero-level hitting times are finite on every compact time interval. The proof requires the renewal/restart and occupation regularity argument, with no replacement process.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.1(i), pp. 105–106.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ZeroVisitsLocallyFiniteV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
      Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ L.X s omega = 0} := by
  sorry
