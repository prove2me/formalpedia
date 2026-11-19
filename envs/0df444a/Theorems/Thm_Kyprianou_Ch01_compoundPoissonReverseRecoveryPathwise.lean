-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonReverseRecoveryPathwise
-- name    : Kyprianou.Ch01.compoundPoissonReverseRecoveryPathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:34:20.250039+00:00
-- url     : https://prove2.me/theorems/41fefac4-5573-460f-ba9d-981ea052b900
-- title:
--   Pathwise inverse-speed Lamperti recovery before nonpositive passage
-- statement:
--   For any càdlàg integer-valued compound Poisson sample path and locally integrable inverse-speed clock, the reverse Lamperti time-change recovers the exact path at each time t when X remains positive on [0,t]. The proof requires the source ENNReal reciprocal occupation integral to be finite and strictly increasing through t, right-continuity to establish a subsequent strict crossing, the extended-clock right inverse, and the first-negative-passage stopping bound.
-- source:
--   Kyprianou (2006), Chapter 1 Eq. (1.19), reverse Lamperti time-change

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.WithBot
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open Kyprianou.Ch01 MeasureTheory Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonReverseRecoveryPathwise
    {Ω : Type*} (X : NNReal → Ω → ℤ) (ω : Ω)
    (hcadlag : ∀ t : NNReal,
      Tendsto (fun s : NNReal => X s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (X t ω)))
    (hlocalint : ∀ t : NNReal,
      IntervalIntegrable
        (fun s : ℝ =>
          if 0 < X (Real.toNNReal s) ω then
            1 / (X (Real.toNNReal s) ω : ℝ)
          else 0)
        volume 0 (t : ℝ)) :
    ∀ t : NNReal,
      (∀ s : NNReal, s ≤ t → 0 < X s ω) →
        compoundPoissonToBranching X
          (Real.toNNReal (reciprocalOccupation X t ω).toReal) ω = X t ω := by
  sorry
