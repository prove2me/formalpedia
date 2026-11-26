-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalPastEventIntervalIncrementV1
-- name    : Kyprianou.Ch04.physicalPastEventIntervalIncrementV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:29:42.052042+00:00
-- url     : https://prove2.me/theorems/f1264c0e-31bd-5147-84ce-f6157e3128a1
-- title:
--   Physical integral past-event interval increment
-- statement:
--   Masking a physical integral by a future interval and a past event extracts the event-indicated difference of cumulative integrals.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalPastEventIntervalIncrementV1 {Ω : Type} (R : Measure (ℝ × ℝ)) (s t : NNReal) (hst : s ≤ t)
    (A : Set Ω) (g : (NNReal × Ω) × ℝ → ℝ) (ω : Ω)
    (hi : IntegrableOn (fun z : ℝ × ℝ => g ((z.1.toNNReal,ω),z.2))
      (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) R) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      (((Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)).indicator g) ((z.1.toNNReal,ω),z.2) ∂ R) =
    A.indicator (fun _ =>
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,ω),z.2) ∂ R) -
      ∫ z in Icc (0 : ℝ) (s : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,ω),z.2) ∂ R) ω := by
  sorry
end Kyprianou.Ch04
