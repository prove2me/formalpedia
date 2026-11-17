-- Prove2me | Theorems.Thm_Kyprianou_Ch07_pathwiseRecurrenceIffReturnsEveryPoint
-- name    : Kyprianou.Ch07.pathwiseRecurrenceIffReturnsEveryPoint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:20:44.871227+00:00
-- url     : https://prove2.me/theorems/f3bc318d-4073-452a-9a52-38d15b21941c
-- title:
--   Theorem 7.5(ii): non-compound-Poisson recurrence iff almost-sure arbitrarily late returns to every neighbourhood
-- statement:
--   Prove the non-compound-Poisson equivalence between infinite occupation times and arbitrarily late close returns to every real target point.
-- source:
--   Kyprianou (2006), Theorem 7.5 parts (i)-(ii), printed p. 184; original PDF p. 193. Source-faithful split of published Chapter 7 theorem 019c587e-28df-4080-8768-8f3ce1280d2f, preserving the noncompound Poisson guard only for recurrence.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.pathwiseRecurrenceIffReturnsEveryPoint
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X) :
    Kyprianou.Ch07.IsRecurrentLevyProcess P X ↔
      ∀ x : Real, ∀ᵐ omega ∂P,
        ∀ epsilon : Real, 0 < epsilon →
          ∀ T : NNReal, ∃ t : NNReal,
            T ≤ t ∧ |X t omega - x| < epsilon := by
  sorry
