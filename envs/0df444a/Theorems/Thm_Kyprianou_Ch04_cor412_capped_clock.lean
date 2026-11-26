-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_capped_clock
-- name    : Kyprianou.Ch04.cor412_capped_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:15:37.18137+00:00
-- url     : https://prove2.me/theorems/44234070-8784-5351-90d0-2fbea86c8896
-- title:
--   Finite representative of a capped extended stopping time is a stopping time
-- statement:
--   Finite representative of a capped extended stopping time is a stopping time.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite representative of the minimum of an extended stopping time and a deterministic cap is a stopping time. -/

theorem Kyprianou.Ch04.cor412_capped_clock
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (F : Filtration NNReal mΩ)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) = min (τ w) (n : WithTop NNReal)) :
    IsStoppingTime F (fun w => (T w : WithTop NNReal)) := by sorry
