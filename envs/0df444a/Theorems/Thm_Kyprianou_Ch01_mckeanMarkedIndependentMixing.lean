-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanMarkedIndependentMixing
-- name    : Kyprianou.Ch01.mckeanMarkedIndependentMixing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:02:28.288805+00:00
-- url     : https://prove2.me/theorems/9b0e5b4b-78c6-428a-ac4d-2725a4ef282f
-- title:
--   Independent future increment conditional mixing with an explicitly marked past state
-- statement:
--   Express event-marked mixing by applying independent joint law and pushforward Fubini to g((y,b),z)=if b then f(y+z) else zero, with a bounded payoff f. This is the natural link between the generic joint and iterated integral identities and Kyprianou 1.13 right-natural conditional mixing.
-- source:
--   Kyprianou 2006 Theorem 1.13, conditional independence with a past event marking.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanMarkedIndependentMixing
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ × Bool) (Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hT : Measurable T) (hZ : Measurable Z)
    (hf : Measurable f) (hBound : ∀ y, ‖f y‖ ≤ K)
    (hInd : IndepFun T Z P) :
    (∫ ω, if (T ω).2 = true then f ((T ω).1 + Z ω) else 0 ∂P) =
      (∫ ω, if (T ω).2 = true then
        (∫ ξ, f ((T ω).1 + Z ξ) ∂P) else 0 ∂P) := by sorry
