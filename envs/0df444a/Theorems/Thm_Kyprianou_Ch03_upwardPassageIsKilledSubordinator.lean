-- Prove2me | Theorems.Thm_Kyprianou_Ch03_upwardPassageIsKilledSubordinator
-- name    : Kyprianou.Ch03.upwardPassageIsKilledSubordinator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T16:43:09.820816+00:00
-- url     : https://prove2.me/theorems/efbe0553-9313-4c41-93e0-f63051918adb
-- title:
--   Corollary 3.14: upward passage is a subordinator or independently killed subordinator
-- statement:
--   The strict upward first-passage process of a spectrally negative Levy process excluding nonincreasing paths is equal in whole-path law to an increasing Levy process independently killed at exponential rate Phi(0). A separate WithTop cemetery state represents killing. If Phi(0)=0 the lifetime is infinite almost surely; if Phi(0)>0 it is finite almost surely.
-- source:
--   Kyprianou (2006), Chapter 3, Corollary 3.14, printed p. 82.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem upwardPassageIsKilledSubordinator
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    exists phi : Real,
      0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi) ∧
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
