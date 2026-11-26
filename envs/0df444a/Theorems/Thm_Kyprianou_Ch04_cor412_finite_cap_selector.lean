-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_finite_cap_selector
-- name    : Kyprianou.Ch04.cor412_finite_cap_selector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:22:24.875321+00:00
-- url     : https://prove2.me/theorems/6743b1e9-564b-58fc-a862-7df6015ffa7b
-- title:
--   Finite time selector realizes the deterministic cap of an extended clock
-- statement:
--   Finite time selector realizes the deterministic cap of an extended clock.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite representative agrees with the cap on the finite event and gives the capped extended clock. -/

theorem Kyprianou.Ch04.cor412_finite_cap_selector
    {Ω : Type} (τ : Ω → WithTop NNReal) (finiteTime : Ω → NNReal)
    (hfin : ∀ w, τ w ≠ ⊤ → τ w = (finiteTime w : WithTop NNReal))
    (n : NNReal) :
    let T : Ω → NNReal := fun w => if τ w ≤ (n : WithTop NNReal) then finiteTime w else n
    (∀ w, (T w : WithTop NNReal) = min (τ w) (n : WithTop NNReal)) := by sorry
