-- Prove2me | Theorems.Thm_Kyprianou_Ch06_continuousOrMarkedLocalTimeAtMaximum
-- name    : Kyprianou.Ch06.continuousOrMarkedLocalTimeAtMaximum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:14:05.40752+00:00
-- url     : https://prove2.me/theorems/fb20c5ac-768d-461f-b73a-e2d0e347eb3d
-- title:
--   Theorem 6.7: continuous local time or exponential marks
-- statement:
--   For a Lévy process adapted to a right-continuous filtration with future increments independent of the information at every earlier deterministic time, prove Theorem 6.7. First, existence and uniqueness up to positive deterministic scale of continuous F-adapted local time at its maximum is equivalent to regularity of zero for [0,∞). Second, in the irregular case, construct an independent extension with arbitrary-rate iid exponential marks at successive discrete maximum contacts, and a suitably enlarged filtration that makes the cumulative marked clock admissible. The compatibility assumptions on the given F exclude anticipative or trivial filtrations which cannot support the original path and its adapted local time.
-- source:
--   Kyprianou (2006), Theorem 6.7(i)–(ii), printed pp. 144–145; two-up PDF pp. 77–78.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_RunningMaximumAndContact
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Theorem 6.7: (i) existence and uniqueness up to positive scale
of continuous local time at the maximum is equivalent to regularity
for the CLOSED positive half-line; (ii) in the irregular regime, local
time is a jump-clock obtained by independently exponential marks
on successive discrete maximum-contact epochs. The independent marks
may live on an explicit extension of the original probability space. -/
theorem continuousOrMarkedLocalTimeAtMaximum
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : NNReal → MeasurableSpace Omega)
    (X : NNReal → Omega → Real)
    (hX : IsRealLevyProcess P X)
    (hF : IsFiltration F ∧ IsRightContinuousFiltration F)
    (hAdapted : ∀ t : NNReal,
      @Measurable Omega Real (F t) inferInstance (X t))
    (hIndependentOfPast : ∀ (s : NNReal) (k : Nat)
      (times : Fin k → NNReal) (A : Fin k → Set Real)
      (B : Set Omega),
      (∀ i, MeasurableSet (A i)) →
      @MeasurableSet Omega (F s) B →
      P {omega | omega ∈ B ∧
        (∀ i : Fin k,
          X (s + times i) omega - X s omega ∈ A i)} =
      P B *
        P {omega | ∀ i : Fin k, X (times i) omega ∈ A i}) :
    ((∃ L : NNReal → Omega → NNReal,
      IsContinuousLocalTimeAtMaximum P F X L ∧
      ∀ L' : NNReal → Omega → NNReal,
        IsContinuousLocalTimeAtMaximum P F X L' →
        ∃ c : Real, 0 < c ∧
          ∀ᵐ omega ∂P, ∀ t : NNReal,
            (L' t omega : Real) = c * (L t omega : Real)) ↔
      IsRegularFor P X 0 (Set.Ici 0)) ∧
    ((IsIrregularFor P X 0 (Set.Ici 0)) →
      ∀ lambda : Real, 0 < lambda →
        ∃ (Q : Measure (Omega × (Nat → NNReal)))
          (Fext : NNReal →
            MeasurableSpace (Omega × (Nat → NNReal)))
          (n : NNReal → Omega → Nat)
          (L : NNReal → (Omega × (Nat → NNReal)) → NNReal),
          IsProbabilityMeasure Q ∧
          Measure.map Prod.fst Q = P ∧
          (∀ t : NNReal, ∀ᵐ z ∂Q,
            L t z = ∑ i ∈ Finset.range (n t z.1 + 1), z.2 i) ∧
          (∀ᵐ omega ∂P, ∀ t : NNReal,
            Set.Finite {s : NNReal |
              0 < s ∧ s ≤ t ∧
                X s omega = runningMaximum X s omega}) ∧
          (∀ᵐ omega ∂P, ∀ t : NNReal,
            n t omega =
              ({s : NNReal |
                0 < s ∧ s ≤ t ∧
                  X s omega = runningMaximum X s omega}).ncard) ∧
          (∀ (i : Nat) (t : NNReal),
            Q {z | t < z.2 i} =
              ENNReal.ofReal (Real.exp (-lambda * (t : Real)))) ∧
          (∀ (k : Nat) (A : Fin k → Set NNReal),
            (∀ i, MeasurableSet (A i)) →
            Q {z | ∀ i : Fin k, z.2 i ∈ A i} =
              ∏ i : Fin k, Q {z | z.2 i ∈ A i}) ∧
          (∀ (k : Nat) (A : Fin k → Set NNReal)
            (B : Set Omega),
            (∀ i, MeasurableSet (A i)) → MeasurableSet B →
            Q {z | z.1 ∈ B ∧
              (∀ i : Fin k, z.2 i ∈ A i)} =
              P B * Q {z | ∀ i : Fin k, z.2 i ∈ A i}) ∧
          IsAdmissibleLocalTimeAtMaximum Q Fext
            (fun t z => X t z.1) L) := by
  sorry

end Kyprianou.Ch06
