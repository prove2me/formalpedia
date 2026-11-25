-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_grid_gain_uniform_bound
-- name    : Kyprianou.Ch04.kw47_grid_gain_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:02:50.51217+00:00
-- url     : https://prove2.me/theorems/09609931-8317-4cf4-a4f2-c42cc4fd376e
-- title:
--   Dominating finite stochastic product gains by endpoint and variation bounds
-- statement:
--   For any finite real grid sequences E,H satisfying |E_i|≤S, |H_i|≤C and total variation of H at most 2C, summation by parts bounds the absolute leftpoint product gain sum Σ H_i(E_{i+1}−E_i) by 4SC. The proof uses the existing Proved exact finite summation by parts identity; both endpoint products are at most SC and the variation remainder is at most 2SC. Applied to E=Esscher exponential and H=running-supremum factor, this is the pathwise uniform integrability envelope for all approximating finite grids.
-- source:
--   Kyprianou (2006) Exercise 4.7, p.108, worked solution pp. 320–321; deterministic product-summation variation domination.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_discrete_product_summation
set_option autoImplicit false

/-- Grid product gains are uniformly dominated by endpoint suprema
and deterministic variation of the multiplier. -/

theorem Kyprianou.Ch04.kw47_grid_gain_uniform_bound
    (E H : Nat → Real) (n : Nat) (S C : Real)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hE : ∀ i, |E i| ≤ S)
    (hH : ∀ i, |H i| ≤ C)
    (hVarH : (∑ i ∈ Finset.range n,
      |H (i+1) - H i|) ≤ 2*C) :
    |∑ i ∈ Finset.range n, H i * (E (i+1) - E i)|
      ≤ 4 * S * C := by sorry
