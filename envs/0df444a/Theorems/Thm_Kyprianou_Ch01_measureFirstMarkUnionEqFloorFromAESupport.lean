-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measureFirstMarkUnionEqFloorFromAESupport
-- name    : Kyprianou.Ch01.measureFirstMarkUnionEqFloorFromAESupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:53:19.592975+00:00
-- url     : https://prove2.me/theorems/e57d7ff9-c98f-48f8-8aa9-0593245f143c
-- title:
--   Almost sure integer-mark support converts the countable mark-event union to the floor-indexed event
-- statement:
--   For an arbitrary real mark m with almost-sure support on {j-1:j natural}, a measurable-space measure Q and any event family F j ω = k with auxiliary predicate B ω, the countable union of marked events has exactly the same Q mass as the single event obtained by setting j=floor(m+1).toNat. This is a purely pathwise index reparametrisation valid without independence or regularity of F or B.
-- source:
--   Generic measure-theoretic bridge used in Kyprianou (2006) §1.3.4 first-arrival renewal expansion

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.measureFirstMarkUnionEqFloorFromAESupport
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (m : Ω → ℝ)
    (hSupport : ∀ᵐ ω ∂Q, ∃ j : ℕ, m ω = (j : ℝ) - 1)
    (F : ℕ → Ω → ℕ) (B : Ω → Prop) (k : ℕ) :
    Q (⋃ j : ℕ, {ω : Ω |
        m ω = (j : ℝ) - 1 ∧ F j ω = k ∧ B ω}) =
      Q {ω : Ω |
        F (Int.floor (m ω + 1)).toNat ω = k ∧ B ω} := by
  sorry
