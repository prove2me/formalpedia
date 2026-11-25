-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_product_grid_variation_bound
-- name    : Kyprianou.Ch04.kw47_product_grid_variation_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:49:48.695545+00:00
-- url     : https://prove2.me/theorems/4ecde32e-f2e5-5de7-bf3f-3e7f93a5cc85
-- title:
--   Uniform product variation from separate factor variation
-- statement:
--   For any finite real grid sequences a,b with |a_i| ≤ 1, |b_i| ≤ C, sum |Δa| ≤ 1 and sum |Δb| ≤ C, the product sequence has total absolute variation at most 2C. Expand Δ(ab) into two terms, apply the triangle inequality and sum the factor bounds. This provides uniform compact-horizon total-variation domination of the Esscher Kella-Whitt integrating factor.
-- source:
--   Elementary product variation inequality used in the deterministic finite-grid summation-by-parts proof of Kyprianou (2006), Exercise 4.7, p.108.

import Mathlib
set_option autoImplicit false

/-- A product of two bounded grid factors has variation controlled
by the separate factor variation and their uniform bounds. -/

theorem Kyprianou.Ch04.kw47_product_grid_variation_bound
    (a b : Nat → Real) (C : Real) (n : Nat)
    (hC : 0 ≤ C)
    (ha : ∀ i, |a i| ≤ 1)
    (hb : ∀ i, |b i| ≤ C)
    (hVA : (∑ i ∈ Finset.range n, |a (i+1) - a i|) ≤ 1)
    (hVB : (∑ i ∈ Finset.range n, |b (i+1) - b i|) ≤ C) :
    (∑ i ∈ Finset.range n,
      |a (i+1) * b (i+1) - a i * b i|) ≤ 2 * C := by sorry
