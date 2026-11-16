-- Prove2me | Theorems.Thm_Kyprianou_Ch06_ascendingLadderTimeDrift
-- name    : Kyprianou.Ch06.ascendingLadderTimeDrift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:06:22.47224+00:00
-- url     : https://prove2.me/theorems/b85de7fb-ac89-483a-907c-57f7f9c1cf43
-- title:
--   Corollary 6.11: drift of ascending ladder time
-- statement:
--   Under the law of a Lévy process with admissible local time L at its maximum, assume the ordinary-time occupation identity ∫₀ᵗ 1(X_s=runningSup_s)ds=aL_t. Show that the right inverse of local time, the ascending ladder-time subordinator of Theorem 6.10, has deterministic drift coefficient a. The drift is formalised through its almost-sure slope at time zero and admits a=0.
-- source:
--   Kyprianou (2006), Corollary 6.11, printed p. 153; physical PDF p. 82; Theorem 6.8 occupation constant.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Corollary 6.11: the ladder-time subordinator has drift equal to the
coefficient a relating ordinary time at the running supremum and local
time. Drift is identified from the small-time slope of its inverse-clock
sample paths, including the case of zero drift. -/
theorem ascendingLadderTimeDrift
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal) (a : NNReal)
    (hX : IsRealLevyProcess P X)
    (hL : IsAdmissibleLocalTimeAtMaximum P F X L)
    (hOccupation : ∀ᵐ omega ∂P, ∀ t : NNReal,
      (∫ s in Set.Icc (0 : NNReal) t,
        if X s omega = runningMaximum X s omega
        then (1 : Real) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) =
          (a : Real) * (L t omega : Real)) :
    ∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal =>
        (inverseLocalTime L t omega).untopD 0 / t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  sorry

end Kyprianou.Ch06
