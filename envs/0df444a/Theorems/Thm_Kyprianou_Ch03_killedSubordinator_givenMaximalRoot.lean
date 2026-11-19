-- Prove2me | Theorems.Thm_Kyprianou_Ch03_killedSubordinator_givenMaximalRoot
-- name    : Kyprianou.Ch03.killedSubordinator_givenMaximalRoot
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T15:40:01.649539+00:00
-- url     : https://prove2.me/theorems/04928f15-70d5-4849-b3b2-e22a09eccd59
-- title:
--   Chapter 3 upward first passage: killed subordinator construction given maximal Laplace-exponent root
-- statement:
--   Given the original spectrally negative Levy hypotheses and a maximal nonnegative zero of the Laplace exponent, construct the original killed-subordinator probability space, independent killing time, survival law, killing regime and full first-passage path-law identity. All original mathematical requirements are retained.
-- source:
--   Kyprianou (2006), Chapter 3, upward passage killed subordinator theorem

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem killedSubordinator_givenMaximalRoot
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (phi : Real)
    (hRoot : 0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) :
    exists (Omega2 : Type) (m2 : MeasurableSpace Omega2),
        letI : MeasurableSpace Omega2 := m2
        exists (Q : Measure Omega2) (hQ : IsProbabilityMeasure Q),
          letI : IsProbabilityMeasure Q := hQ
          exists (S : NNReal -> Omega2 -> Real)
                 (zeta : Omega2 -> WithTop NNReal),
            IsSubordinator Q S ∧
            Indep
              (MeasurableSpace.comap zeta
                (inferInstance : MeasurableSpace (WithTop NNReal)))
              (MeasurableSpace.comap
                (fun omega : Omega2 => fun x : NNReal => S x omega)
                (inferInstance : MeasurableSpace (NNReal -> Real)))
              Q ∧
            (forall x : NNReal,
              (Q {omega : Omega2 |
                (x : WithTop NNReal) < zeta omega}).toReal =
                  Real.exp (-phi * (x : Real))) ∧
            (phi = 0 ->
              (Q {omega : Omega2 | zeta omega = ⊤}).toReal = 1) ∧
            (0 < phi ->
              (Q {omega : Omega2 | zeta omega != ⊤}).toReal = 1) ∧
            Measure.map
              (fun omega : Omega =>
                fun x : NNReal =>
                  firstHittingTime L.X (Set.Ioi (x : Real)) omega) P =
            Measure.map
              (fun omega : Omega2 =>
                fun x : NNReal =>
                  if (x : WithTop NNReal) < zeta omega
                  then (Real.toNNReal (S x omega) : WithTop NNReal)
                  else ⊤) Q := by
  sorry

end Kyprianou.Ch03
