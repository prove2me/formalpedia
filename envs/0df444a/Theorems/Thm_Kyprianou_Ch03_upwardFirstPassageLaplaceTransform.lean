-- Prove2me | Theorems.Thm_Kyprianou_Ch03_upwardFirstPassageLaplaceTransform
-- name    : Kyprianou.Ch03.upwardFirstPassageLaplaceTransform
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T16:42:11.262853+00:00
-- url     : https://prove2.me/theorems/1dd49557-7191-4dc6-9514-a2f27e94bec6
-- title:
--   Theorem 3.12: Laplace transform of strict upward first-passage time
-- statement:
--   For spectrally negative Levy processes that are not almost surely nonincreasing, each q>=0 admits a largest nonnegative root phi of psi(phi)=q. For every x>=0, the expected exp(-q*tau_x^+) on finite strict upward passage equals exp(-phi*x), assigning value zero to infinite passage including q=0. Finite-time representatives do not restrict the stopping time.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.12, printed pp. 81-82; excludes the mathematically invalid decreasing-path edge case left implicit in the textbook.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem upwardFirstPassageLaplaceTransform
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    forall (q : Real), 0 <= q ->
      exists phi : Real,
        0 <= phi ∧ L.ψ phi = q ∧
        (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi) ∧
        (forall (x : Real), 0 <= x ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) := by
  sorry

end Kyprianou.Ch03
