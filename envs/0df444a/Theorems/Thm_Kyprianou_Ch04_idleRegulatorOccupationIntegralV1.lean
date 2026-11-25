-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorOccupationIntegralV1
-- name    : Kyprianou.Ch04.idleRegulatorOccupationIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:25:05.644773+00:00
-- url     : https://prove2.me/theorems/28462c44-29a3-474b-abb1-da0bf8084507
-- title:
--   Lipschitz regulator derivative integrates to its occupation reward
-- statement:
--   A Lipschitz function is absolutely continuous on the finite interval. The fundamental theorem of calculus and a.e. derivative equality give the real integral of the bounded measurable contact indicator. Convert this nonnegative integral to an ENNReal lintegral.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic regulator calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleRegulatorOccupationIntegralV1
    (R f : Real → Real) (d T : Real) (hd : 0 < d) (hT : 0 ≤ T)
    (hLip : LipschitzWith (Real.toNNReal d) R) (hf : Measurable f)
    (hder : ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      deriv R t = if R t - f t = 0 then d else 0) :
    ENNReal.ofReal (R T - R 0) =
      ENNReal.ofReal d * (∫⁻ t in Icc (0 : Real) T,
        (if R t - f t = 0 then (1 : ENNReal) else 0) ∂volume) := by
  sorry
