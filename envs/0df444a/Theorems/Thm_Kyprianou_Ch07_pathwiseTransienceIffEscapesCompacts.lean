-- Prove2me | Theorems.Thm_Kyprianou_Ch07_pathwiseTransienceIffEscapesCompacts
-- name    : Kyprianou.Ch07.pathwiseTransienceIffEscapesCompacts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:20:48.284905+00:00
-- url     : https://prove2.me/theorems/4960abc4-2078-461b-8535-55469c320c36
-- title:
--   Theorem 7.5(i): transience iff the absolute Lévy process escapes to infinity
-- statement:
--   Prove the equivalence between almost-sure finite occupation of every compact interval and almost-sure escape of the process in absolute value.
-- source:
--   Kyprianou (2006), Theorem 7.5 parts (i)-(ii), printed p. 184; original PDF p. 193. Source-faithful split of published Chapter 7 theorem 019c587e-28df-4080-8768-8f3ce1280d2f, preserving the noncompound Poisson guard only for recurrence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.pathwiseTransienceIffEscapesCompacts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    :
    Kyprianou.Ch07.IsTransientLevyProcess P X ↔
      ∀ᵐ omega ∂P,
        Tendsto (fun t : NNReal => |X t omega|) atTop atTop := by
  sorry
