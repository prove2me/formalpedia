-- Prove2me | Theorems.Thm_Kyprianou_Ch04_fullCutoffTerminalL2ClosureV1
-- name    : Kyprianou.Ch04.fullCutoffTerminalL2ClosureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:53:15.254593+00:00
-- url     : https://prove2.me/theorems/02417deb-cf88-4cf8-978b-221b1fcd0038
-- title:
--   Terminal L2 closure of a square Cauchy cutoff family
-- statement:
--   The terminal almost-sure subsequential limit of a square Cauchy family is square integrable, and the whole cutoff family converges to it in L2.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem fullCutoffTerminalL2ClosureV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → Ω → ℝ) (M : Ω → ℝ) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n ∧ e n < 1) (he0 : Tendsto e atTop (𝓝 0))
    (hm : ∀ a, 0 < a → a < 1 → Measurable (Y a))
    (hi : ∀ a, 0 < a → a < 1 → Integrable (fun w => (Y a w)^2) P)
    (hM : Measurable M)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => Y (e n) w) atTop (𝓝 (M w)))
    (hc : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ a b, 0 < a → a < r → 0 < b → b < r →
        (∫ w, (Y a w - Y b w)^2 ∂P) ≤ δ) :
    Integrable (fun w => (M w)^2) P ∧
      Tendsto (fun a => ∫ w, (Y a w - M w)^2 ∂P) (𝓝[>] 0) (𝓝 0) := by
  sorry
end Kyprianou.Ch04
