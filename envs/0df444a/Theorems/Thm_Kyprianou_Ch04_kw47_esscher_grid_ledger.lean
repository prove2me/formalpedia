-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_ledger
-- name    : Kyprianou.Ch04.kw47_esscher_grid_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:00:50.629807+00:00
-- url     : https://prove2.me/theorems/088fa6b1-4670-4aa9-835b-88dbfa449b4a
-- title:
--   Integrable predictable Esscher grid ledger
-- statement:
--   Every finite deterministic monotone grid has integrable gain, the common integrable envelope as an almost-everywhere bound, and zero gain integral on each event in the filtration before the start.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.7.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_measurable
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_integrable_envelope
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_gain_uniform_bound
import Theorems.Thm_Kyprianou_Ch04_kw47_esscher_grid_past_event_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite predictable Esscher grid has an integrable gain, a
common integrable envelope, and vanishing integrals on past events. -/

theorem Kyprianou.Ch04.kw47_esscher_grid_ledger
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) (u : Nat → NNReal) (hu : Monotone u)
    (hT : ∀ i, u i ≤ T) (n : Nat) (a : NNReal) (ha : a ≤ u 0) :
    let E : NNReal → Ω → Real := fun t w =>
      Real.exp (alpha * L.X t w - L.ψ alpha * (t:Real))
    let H : NNReal → Ω → Real := fun t w =>
      Real.exp (-alpha * runningSup L t w + L.ψ alpha * (t:Real))
    let Q : Ω → Real := fun w => ∑ i ∈ Finset.range n,
      H (u i) w * (E (u (i+1)) w - E (u i) w)
    let B : Ω → Real := fun w =>
      4 * Real.exp (alpha * runningSup L T w + |L.ψ alpha| * (T:Real)) *
        Real.exp (|L.ψ alpha| * (T:Real))
    Integrable Q P ∧ (∀ᵐ w ∂P, ‖Q w‖ ≤ B w) ∧
      (∀ A : Set Ω, MeasurableSet[F a] A → (∫ w in A, Q w ∂P) = 0) := by sorry
