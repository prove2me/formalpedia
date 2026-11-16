-- Prove2me | Theorems.Thm_Kyprianou_Ch06_maximumOccupationCoefficientCriterion
-- name    : Kyprianou.Ch06.maximumOccupationCoefficientCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:07:11.354348+00:00
-- url     : https://prove2.me/theorems/87a8c108-623a-421e-8960-7ca03bf4dad2
-- title:
--   Theorem 6.8: positivity of maximum-occupation drift
-- statement:
--   Suppose X is a real Lévy process with the origin regular for the closed positive half-line, and L is any continuous local time at its running maximum. For the nonnegative coefficient a defined by ∫₀ᵗ1(X_s=runningSup_s)ds=aL_t, prove that a>0 if and only if X has sample paths of bounded variation on compact time intervals and zero is irregular for (-∞,0). Both directions and the a=0 alternative are included.
-- source:
--   Kyprianou (2006), Theorem 6.8, printed p. 146; physical PDF p. 78.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Theorem 6.8: ordinary time at the running supremum is a positive
multiple of local time exactly for bounded-variation Levy processes that
are irregular at zero for the open negative half-line. Bounded variation
is specified by uniform bounds for every finite sample-path partition. -/
theorem maximumOccupationCoefficientCriterion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal) (a : NNReal)
    (hX : IsRealLevyProcess P X)
    (hClosedRegular : IsRegularFor P X 0 (Set.Ici 0))
    (hL : IsContinuousLocalTimeAtMaximum P F X L)
    (hOccupation : ∀ᵐ omega ∂P, ∀ t : NNReal,
      (∫ s in Set.Icc (0 : NNReal) t,
        if X s omega = runningMaximum X s omega
        then (1 : Real) else 0 ∂(Measure.map Real.toNNReal (volume.restrict (Set.Ici (0 : Real))))) =
          (a : Real) * (L t omega : Real)) :
    (0 < a ↔
      ((∀ᵐ omega ∂P, ∀ T : NNReal,
          ∃ C : Real, 0 ≤ C ∧
            ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
              StrictMono times → times (Fin.last n) ≤ T →
              (∑ i : Fin n,
                |X (times i.succ) omega -
                  X (times i.castSucc) omega|) ≤ C) ∧
        IsIrregularFor P X 0 (Set.Iio 0))) := by
  sorry

end Kyprianou.Ch06
