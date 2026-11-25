-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvDyadicDeficitZeroAeTimeV1
-- name    : Kyprianou.Ch04.bvDyadicDeficitZeroAeTimeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:14:33.859795+00:00
-- url     : https://prove2.me/theorems/e9bd5e1d-9a65-4089-b346-0be20f7769a4
-- title:
--   BV drift deficit has zero dyadic right slope for almost every time
-- statement:
--   Use the proved BV zero-deficit origin path cylinder event and deterministic shifted-path law, then commute the almost-everywhere quantifiers by measurable joint evaluation and Fubini. No first-moment or standing assumptions are needed.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, proof of idle-time regulator identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
open Set

theorem Kyprianou.Ch04.bvDyadicDeficitZeroAeTimeV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) :
    ∀ᵐ omega ∂P, ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      Tendsto (fun n : Nat =>
        (L.drift * ((((1 : NNReal) / 2) ^ n : NNReal) : Real) -
          (L.X (Real.toNNReal t + ((1 : NNReal) / 2) ^ n) omega -
            L.X (Real.toNNReal t) omega)) /
          ((((1 : NNReal) / 2) ^ n : NNReal) : Real))
        atTop (𝓝 (0 : Real)) := by
  sorry
