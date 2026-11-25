-- Prove2me | Theorems.Thm_Kyprianou_Ch04_downwardPassageJointDeficitTailBV
-- name    : Kyprianou.Ch04.downwardPassageJointDeficitTailBV
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T18:02:23.621326+00:00
-- url     : https://prove2.me/theorems/541deb06-96f6-48ad-9cc9-737216d76b39
-- title:
--   Source-faithful integrated-tail joint deficit distribution before ruin
-- statement:
--   For the same process, the joint probability that first downward passage is finite and the undershoot deficit is at most x is the integrated Levy negative tail on [0,x] divided by d.
-- source:
--   Kyprianou (2006), Corollary 4.12, page 105, integrated-tail identity.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.downwardPassageJointDeficitTailBV
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (hMeanPositive :
      0 < derivWithin L.ψ (Set.Ici (0 : Real)) 0) :
    let tau : Omega → WithTop NNReal := fun omega =>
      Kyprianou.Ch03.firstHittingTime L.X (Set.Iio 0) omega
    ∀ (finiteTime : Omega → NNReal),
      (∀ omega : Omega, tau omega ≠ ⊤ →
        tau omega = (finiteTime omega : WithTop NNReal)) →
      ∀ x : Real, 0 ≤ x →
        let ruinAndDeficit : Set Omega :=
          {omega : Omega |
            tau omega ≠ ⊤ ∧
              -(L.X (finiteTime omega) omega) ≤ x}
        let integratedTail : Real :=
          ∫ y in Set.Icc (0 : Real) x,
            (L.ν (Set.Iio (-y))).toReal ∂volume
        (P ruinAndDeficit).toReal =
          (1 / L.drift) * integratedTail := by
  sorry
