-- Prove2me | Theorems.Thm_Kyprianou_Ch07_pathwiseTransienceRecurrenceCharacterisation
-- name    : Kyprianou.Ch07.pathwiseTransienceRecurrenceCharacterisation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:44:43.38584+00:00
-- url     : https://prove2.me/theorems/019c587e-28df-4080-8768-8f3ce1280d2f
-- title:
--   Theorem 7.5: pathwise transience and recurrence characterisation
-- statement:
--   Theorem 7.5(i): for every Lévy process, occupation transience is equivalent to |X_t| tending to infinity almost surely as t tends to infinity. Theorem 7.5(ii): for a non-compound-Poisson Lévy process, occupation recurrence is equivalent to the property that for every x in the real line, liminf as t tends to infinity of |X_t-x| is zero almost surely. The per-point probability-one quantifier and non-compound-Poisson restriction are retained.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.5(i)–(ii), printed p.184; Windows Ky.pdf landscape sheet 97 (original single-page PDF p.193).

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.5(i)-(ii): probabilistic path characterisations
of occupation transience and recurrence. -/
theorem pathwiseTransienceRecurrenceCharacterisation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X) :
    ((IsTransientLevyProcess P X ↔
      ∀ᵐ omega ∂P,
        Tendsto (fun t : NNReal => |X t omega|) atTop atTop) ∧
     (¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X →
      (IsRecurrentLevyProcess P X ↔
        ∀ x : Real, ∀ᵐ omega ∂P,
          ∀ epsilon : Real, 0 < epsilon →
            ∀ T : NNReal, ∃ t : NNReal,
              T ≤ t ∧ |X t omega - x| < epsilon))) := by
  sorry

end Kyprianou.Ch07
