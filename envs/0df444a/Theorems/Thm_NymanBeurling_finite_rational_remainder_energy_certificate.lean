-- Prove2me | Theorems.Thm_NymanBeurling_finite_rational_remainder_energy_certificate
-- name    : NymanBeurling.finite_rational_remainder_energy_certificate
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:33:44.660685+00:00
-- url     : https://prove2.me/theorems/34bb47f1-c2d3-49cd-932c-a10ef765190b
-- title:
--   A 64-term Bagchi certificate of squared error less than one hundredth
-- statement:
--   There is an explicit vector with exactly 64 nonzero rational coefficients at denominators at most 240. For the Bagchi remainder $R(m)=1-\sum_d c_d(m\bmod d)/d$, every finite prefix of $\sum_{m\ge1}R(m)^2/[m(m+1)]$ is less than $1/100$. The proof gives the uniform bound $994/100000$, including for the infinite series. Even the elementary finite rational certificate at $K=10^8$, formed by adding $(1+\sum_d|c_d|)^2/(K+1)$ to the $K$-term prefix, is strictly below $1/100$. Thus one fixed vector verifies every accuracy index $J\le99$ of the subpower-certificate frontier at arbitrarily large lower cutoffs $L$. Arbitrary $J$ remains the open arithmetic condition.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146. Partial quantitative case of NymanBeurling.subpower_remainder_certificates, Prove2Me 28d55614-fcbe-4180-a244-028572cf1883.

import Mathlib

open Finset

theorem NymanBeurling.finite_rational_remainder_energy_certificate :
    ∃ c : ℕ →₀ ℚ, c.support.card = 64 ∧ (∀ k ∈ c.support, k+2 ≤ 240) ∧
      (let R := fun n : ℕ => 1 - ∑ k ∈ c.support, c k * ((((n+1) % (k+2) : ℕ) : ℚ) / (k+2 : ℚ))
       let E := fun n : ℕ => (R n)^2 / ((n+1 : ℚ)*(n+2 : ℚ))
       let C := (∑ n ∈ Finset.range 100000000, E n) + (1 + ∑ k ∈ c.support, |c k|)^2/100000001
       C < 1/100 ∧
       (∀ H : ℕ, ∑ n ∈ Finset.range H, E n < 1/100) ∧
       ∀ (J L : ℕ), J ≤ 99 → ∃ H : ℕ, L ≤ H ∧
         (∑ n ∈ Finset.range H, E n) ≤ 1/(J+1 : ℚ) ∧ C^(J+1) ≤ (H+1 : ℚ)) := by sorry
