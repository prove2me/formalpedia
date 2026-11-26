-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46JumpFreeLeftAffineV1
-- name    : Kyprianou.Ch04.exercise46JumpFreeLeftAffineV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:16:18.262923+00:00
-- url     : https://prove2.me/theorems/8cd35528-30d2-5bd0-a9f4-c3e18702e6be
-- title:
--   Left limits of a finite-activity unit-drift path are locally affine from the left
-- statement:
--   On each finite horizon the jump set is finite. Choose a strict left gap at t; the proved jump-free drift identity holds throughout it. Taking the left limit at any u in the gap gives the claimed affine expression.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46JumpFreeLeftAffineV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hBV : L.BoundedVariation) (hDrift : L.drift = 1)
    (hFinite : L.ν (Iio (0 : Real)) < ⊤) :
    ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      ∃ s : NNReal, s < t ∧ ∀ u : NNReal, s < u → u ≤ t →
        Function.leftLim (fun v : NNReal => L.X v w) u =
          L.X s w + ((u : Real) - (s : Real)) := by
  sorry
