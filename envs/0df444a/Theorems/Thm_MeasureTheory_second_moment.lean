-- Prove2me | Theorems.Thm_MeasureTheory_second_moment
-- name    : MeasureTheory.second_moment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:29:42.251837+00:00
-- url     : https://prove2.me/theorems/98bc50b9-5746-4cc8-aa35-07d15cdf7a53
-- title:
--   Measure Theory: second moment
-- statement:
--   **The second-moment bound.** See the module docstring.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/SecondMoment.lean#L79-L192
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/SecondMoment.lean#L79-L192

module
public import Definitions.Def_AddUN_CantorMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_AddUN_SecondMoment
set_option autoImplicit false
@[expose] public section
public section
open Set MeasureTheory
open MeasureTheory

theorem MeasureTheory.second_moment {K : Set (ℕ → Bool)} (hK : MeasurableSet K) (J : Finset ℕ)
    (E : ℕ → Set (ℕ → Bool)) (B : ℕ → Finset ℕ) (v : ℕ → Bool) (L : ℕ) (s : Set ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hE : ∀ k ∈ J, MeasurableSet (E k)) (hdet : ∀ k ∈ J, Determined s (E k))
    (hs : ∀ k ∈ J, Disjoint s (B k : Set ℕ))
    (hB : ∀ k ∈ J, ∀ k' ∈ J, k ≠ k' → Disjoint (B k) (B k')) (hL : ∀ k ∈ J, (B k).card = L)
    (hθK : ∀ k ∈ J, θ ≤ cantorMeasure.real (K ∩ E k))
    (hbad : ∀ k ∈ J, cantorMeasure.real (K ∩ E k ∩ cylinderOn (B k) v) ≤
      (1 / 2) ^ L / 2 * cantorMeasure.real (K ∩ E k)) :
    (J.card : ℝ) * (1 / 2) ^ L * θ ^ 2 ≤ 4 := by sorry
