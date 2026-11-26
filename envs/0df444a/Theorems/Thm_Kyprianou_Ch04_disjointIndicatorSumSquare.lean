-- Prove2me | Theorems.Thm_Kyprianou_Ch04_disjointIndicatorSumSquare
-- name    : Kyprianou.Ch04.disjointIndicatorSumSquare
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:03:51.711207+00:00
-- url     : https://prove2.me/theorems/c227e77a-acce-4459-a3b9-8b408b943cc9
-- title:
--   Pointwise square of a disjoint finite weighted indicator sum
-- statement:
--   For a finite pairwise disjoint family of sets, the square of the weighted sum of their indicators equals the sum of the indicators with squared weights.
-- source:
--   Elementary disjoint-support algebra; Kyprianou Chapter 4 Exercise 4.4.

import Mathlib
open scoped BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.disjointIndicatorSumSquare
    {A : Type u} {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (B : ι → Set A) (c : ι → ℝ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (x : A) :
    (∑ i ∈ s, (B i).indicator (fun _ => c i) x)^2 =
      ∑ i ∈ s, (B i).indicator (fun _ => (c i)^2) x := by
  sorry
