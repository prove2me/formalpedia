-- Prove2me | Theorems.Thm_Kyprianou_Ch06_compoundPoissonOfBothExtremalOccupations
-- name    : Kyprianou.Ch06.compoundPoissonOfBothExtremalOccupations
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:05:38.723054+00:00
-- url     : https://prove2.me/theorems/0d2691cc-6293-489f-8cf3-cd5cb010ccb7
-- title:
--   Exercise 6.4: positive occupation at both extrema implies compound Poisson
-- statement:
--   For a real Lévy process, suppose that almost every sample path has positive (possibly infinite) Lebesgue occupation time at its running maximum and also at its running minimum. Show that the process must be compound Poisson, with zero linear drift. Both occupation times are retained as part of the single source exercise.
-- source:
--   Kyprianou (2006), Exercise 6.4, printed p. 175; two-up PDF p. 93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.4: simultaneous positive Lebesgue occupation times at the
running supremum and infimum characterise the compound Poisson case. -/
theorem compoundPoissonOfBothExtremalOccupations
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hOccupations :
      P {omega |
        (∫⁻ t : NNReal,
          if X t omega = runningMaximum X t omega
          then (1 : ENNReal) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) > 0 ∧
        (∫⁻ t : NNReal,
          if X t omega =
            sInf ((fun u : NNReal => X u omega) '' Set.Icc 0 t)
          then (1 : ENNReal) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) > 0} = 1) :
    IsCompoundPoissonProcess P X := by
  sorry

end Kyprianou.Ch06
