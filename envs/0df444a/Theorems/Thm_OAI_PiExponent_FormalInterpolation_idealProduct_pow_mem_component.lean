-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_idealProduct_pow_mem_component
-- name    : OAI.PiExponent.FormalInterpolation.idealProduct_pow_mem_component
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:14:34.560841+00:00
-- url     : https://prove2.me/theorems/de78f5de-2cca-412f-9ada-714a7478ad0b
-- title:
--   Membership in a product ideal power implies membership in each factor power
-- statement:
--   An element of the nth power of a finite product of ideals belongs to the nth power of each individual factor.

import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.idealProduct_pow_mem_component {A : Type} [CommSemiring A] {K : Nat} (I : Fin K → Ideal A) (x : A) (n : Nat) (j : Fin K) (hx : x ∈ (∏ k : Fin K, I k) ^ n) : x ∈ I j ^ n := by sorry
