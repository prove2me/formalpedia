-- Prove2me | Theorems.Thm_Kyprianou_Ch06_excursionPointProcessWithPossibleKilling
-- name    : Kyprianou.Ch06.excursionPointProcessWithPossibleKilling
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:16:15.194197+00:00
-- url     : https://prove2.me/theorems/4e749000-a846-4afe-9ef3-484805d87ba7
-- title:
--   Theorem 6.15: excursion Poisson process and infinite-excursion killing
-- statement:
--   Construct a sigma-finite excursion intensity n and a measurable path space detecting excursion lifetime, terminal value and height, as in Definition 6.14. (i) For a Lévy process whose running supremum is unbounded at infinity, prove that its actual indexed non-cemetery excursions have the full local-time-marked Poisson point-process law with intensity ds⊗n. (ii) When the supremum is bounded, prove its stopped finite-dimensional excursion-count laws equal those of a Poisson point process of the same intensity stopped at the first excursion of infinite lifetime. All three source conclusions are required. The excursion sigma-algebra is existentially quantified rather than inherited from the product sigma-algebra on an unrestricted function space. Measurability of the excursion domain, lifetime, terminal value and height is explicitly required in the chosen sigma-algebra.
-- source:
--   Kyprianou (2006), Theorem 6.15, printed pp. 155–156; physical PDF p. 83.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
import Definitions.Def_Kyprianou_Ch06_ExcursionSpace
import Definitions.Def_Kyprianou_Ch06_ExcursionCountAtLocalTime
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_AdmissibleLocalTime
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Theorem 6.15: there is a sigma-finite excursion intensity on a rich
measurable excursion path space. Without killing the actual local-time
excursion count is a marked Poisson point process; with finite terminal
local time it agrees in all finite-dimensional stopped count laws with
a Poisson point process stopped at its first infinite-life mark. -/
theorem excursionPointProcessWithPossibleKilling
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (F : NNReal → MeasurableSpace Omega)
    (L : NNReal → Omega → NNReal)
    (hX : IsRealLevyProcess P X)
    (hLocal : IsAdmissibleLocalTimeAtMaximum P F X L) :
    ∃ (Sigma : MeasurableSpace
        ((NNReal → Real) × WithTop NNReal)),
      letI : MeasurableSpace
        ((NNReal → Real) × WithTop NNReal) := Sigma
      ∃ (n : Measure ((NNReal → Real) × WithTop NNReal))
        (cover : Nat → Set ((NNReal → Real) × WithTop NNReal)),
      (∀ k, MeasurableSet (cover k) ∧ n (cover k) < ⊤) ∧
      (⋃ k, cover k) = Set.univ ∧
      MeasurableSet ExcursionSpace ∧
      n ExcursionSpaceᶜ = 0 ∧
      Measurable (fun e : (NNReal → Real) × WithTop NNReal => e.2) ∧
      Measurable (fun e : (NNReal → Real) × WithTop NNReal =>
        e.1 (e.2.untopD 0)) ∧
      Measurable (fun e : (NNReal → Real) × WithTop NNReal =>
        -sInf (e.1 '' {t : NNReal |
          0 < t ∧ (t : WithTop NNReal) < e.2})) ∧
      (P {omega |
        ¬ BddAbove (Set.range (fun t : NNReal => X t omega))} = 1 →
        IsMarkedPoissonPointProcess P n
          (fun omega t A =>
            excursionCountAtLocalTime X L omega t A)) ∧
      (P {omega |
        BddAbove (Set.range (fun t : NNReal => X t omega))} = 1 →
        ∃ Q : Measure
          (NNReal → Option ((NNReal → Real) × WithTop NNReal)),
          IsProbabilityMeasure Q ∧
          IsMarkedPoissonPointProcess Q n
            (fun z t A =>
              ({s : NNReal | 0 < s ∧ s ≤ t ∧
                ∃ e, z s = some e ∧ e ∈ A}).ncard) ∧
          (∀ (k : Nat) (times : Fin k → NNReal)
            (A : Fin k → Set ((NNReal → Real) × WithTop NNReal))
            (counts : Fin k → Nat),
            (∀ i, MeasurableSet (A i) ∧ n (A i) < ⊤) →
            P {omega | ∀ i : Fin k,
              ({s : NNReal |
                0 < s ∧ s ≤ times i ∧
                (s : WithTop NNReal) <
                  sSup ((fun u : NNReal =>
                    (L u omega : WithTop NNReal)) '' Set.univ) ∧
                ∃ e, indexedExcursion X L s omega =
                  some e ∧ e ∈ A i}).ncard = counts i} =
            Q {z | ∀ i : Fin k,
              ({s : NNReal | 0 < s ∧ s ≤ times i ∧
                (s : WithTop NNReal) <
                  sInf ((fun u : NNReal => (u : WithTop NNReal)) ''
                    {u : NNReal | 0 < u ∧
                      ∃ e, z u = some e ∧ e.2 = ⊤}) ∧
                ∃ e, z s = some e ∧ e ∈ A i}).ncard =
                counts i})) := by
  sorry

end Kyprianou.Ch06
