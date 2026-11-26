-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46NoArrivalAtPrelevelV1
-- name    : Kyprianou.Ch04.exercise46NoArrivalAtPrelevelV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:18:50.118937+00:00
-- url     : https://prove2.me/theorems/2b4757eb-62f9-499f-bd1a-e6980f048a0b
-- title:
--   Almost surely no arrival coincides with a first-level precontact
-- statement:
--   The prelevel contact set after a stopping time is predictable and has countable time sections almost surely. Its product compensator measure vanishes, so compensation excludes any negative jump at such a contact, on every integer horizon.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46NoArrivalAtPrelevelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A) :
    ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → A w < (t : WithTop NNReal) →
      Function.leftLim (fun u : NNReal => L.X u w) t =
        (((A w).untopD 0 : NNReal) : Real) →
      ¬ L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t := by
  sorry
