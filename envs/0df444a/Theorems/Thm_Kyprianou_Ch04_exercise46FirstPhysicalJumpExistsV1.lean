-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstPhysicalJumpExistsV1
-- name    : Kyprianou.Ch04.exercise46FirstPhysicalJumpExistsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T22:10:52.925314+00:00
-- url     : https://prove2.me/theorems/fd4db653-24e7-4679-8189-3aa6880726dd
-- title:
--   First physical negative jump is attained at positive finite time
-- statement:
--   Exponential no-jump probabilities imply a jump exists almost surely; locally finite physical jump support supplies an earliest jump, and spectral negativity gives its strict sign.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstPhysicalJumpExistsV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (hBV : L.BoundedVariation)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (hRate : 0 < (L.ν (Iio (0 : Real))).toReal) :
    ∀ᵐ w ∂P, ∃ t : NNReal, 0 < t ∧
      L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t ∧
      ∀ u : NNReal, 0 < u → u < t →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u := by
  sorry
