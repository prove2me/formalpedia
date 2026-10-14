-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_linearMap_vanishes_on_ideal_power_of_products
-- name    : OAI.PiExponent.FormalInterpolation.linearMap_vanishes_on_ideal_power_of_products
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T07:56:12.269717+00:00
-- url     : https://prove2.me/theorems/532a2a58-6e41-4816-bf44-be76ac8c67d0
-- title:
--   Linear maps vanishing on products vanish on positive ideal powers
-- statement:
--   For a positive integer $n$, a $\mathbb C$-linear map that vanishes on every product of $n$ elements of an ideal also vanishes on the entire $n$th ideal power.

import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

theorem OAI.PiExponent.FormalInterpolation.linearMap_vanishes_on_ideal_power_of_products
    {A V : Type} [CommRing A] [AddCommMonoid V] [Module Complex V] [Algebra Complex A]
    (I : Ideal A) (n : Nat) (hn : 0 < n) (F : A →ₗ[Complex] V)
    (hProducts : ∀ f : Fin n → A, (∀ i, f i ∈ I) → F (∏ i, f i) = 0)
    (P : A) (hP : P ∈ I ^ n) : F P = 0 := by sorry
