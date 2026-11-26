-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_independent_weight_integral
-- name    : Kyprianou.Ch04.kw48_independent_weight_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:35.637018+00:00
-- url     : https://prove2.me/theorems/551082e0-d1c2-4172-9af1-5ea416447677
-- title:
--   Complex product integral factorisation across independent past and increment
-- statement:
--   Complex product integral factorisation across independent past and increment.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

/-- Independence from a sub-sigma-algebra factorises the integral
of a transformed future increment times a measurable past weight. -/

theorem Kyprianou.Ch04.kw48_independent_weight_integral
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (G : Ω → Real) (W : Ω → Complex) (phi : Real → Complex)
    (hG : @Measurable Ω Real mΩ inferInstance G)
    (hW : @Measurable Ω Complex m inferInstance W)
    (hphi : Measurable phi)
    (hind : Indep (MeasurableSpace.comap G inferInstance) m P) :
    (∫ w, phi (G w) * W w ∂P) =
      (∫ w, phi (G w) ∂P) * (∫ w, W w ∂P) := by sorry
