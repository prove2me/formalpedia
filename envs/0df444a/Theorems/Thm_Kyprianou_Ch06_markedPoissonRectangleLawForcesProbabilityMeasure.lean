-- Prove2me | Theorems.Thm_Kyprianou_Ch06_markedPoissonRectangleLawForcesProbabilityMeasure
-- name    : Kyprianou.Ch06.markedPoissonRectangleLawForcesProbabilityMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:21:00.224497+00:00
-- url     : https://prove2.me/theorems/e19c8af9-f835-4818-b2fb-08c3fdf0793a
-- title:
--   The Chapter 6 marked Poisson rectangle axiom implies a probability measure
-- statement:
--   The authentic Chapter 6 marked-Poisson point-process finite-rectangle law itself implies that the underlying sample measure P has total mass one. Specialise the exact joint Poisson law to the empty family of rectangles, whose event is the entire sample space and whose empty probability product equals one. Thus IsProbabilityMeasure P follows from the original axiom with no new assumption, enabling null-intensity and almost-sure count lemmas under the original arbitrary Measure P binder.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.markedPoissonRectangleLawForcesProbabilityMeasure
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    IsProbabilityMeasure P := by sorry
