-- Prove2me | Theorems.Thm_NymanBeurling_large_sieve_remainder_tail
-- name    : NymanBeurling.large_sieve_remainder_tail
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:57:32.879475+00:00
-- url     : https://prove2.me/theorems/295f2c4e-09ec-48e0-bdfa-9961fa11b1b5
-- title:
--   A sharp large-sieve bound for finite Bagchi residuals and a uniform computable tail certificate
-- statement:
--   For real coefficients $c_d$ at finitely many integer denominators $1\le d\le D$, put $R(m)=1-\sum_d c_d(m\bmod d)/d$ and let $M$ be its mean square over a full period. Explicitly,
--   $$M=\left(1-\sum_d\frac{c_d(d-1)}{2d}\right)^2+\sum_{d,e}\frac{c_dc_e(\gcd(d,e)^2-1)}{12de}.$$
--   For all nonnegative integer starts $a$ and lengths $L$,
--   $$\sum_{a<m\le a+L} R(m)^2\le(L+D^2)M.$$
--   Consequently, for each $H\ge0$, the summable weighted tail and every finite portion starting there satisfy
--   $$\sum_{m>H}\frac{R(m)^2}{m(m+1)}\le M\left(\frac1{H+1}+\frac{D^2}{(H+1)(H+2)}\right).$$
--   The bound is uniform over all coefficient choices and independent of the least common multiple of the denominators. Together with a finite prefix calculation, it bounds the actual Bagchi norm in the rational certificate frontier.
-- source:
--   Finite Bagchi Hilbert-space criterion for the Masullo RH specialization. The prefix weights are those of B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146. The sharp additive large sieve is applied through the Prove2Me theorem TaoFivePrimes.large_sieve_inequality_spacing_le_one.

import Mathlib

open Finset

theorem NymanBeurling.large_sieve_remainder_tail (S : Finset ℕ) (c : ℕ → ℝ) (D : ℕ)
    (hD : 0 < D) (hs : ∀ d ∈ S, 0 < d ∧ d ≤ D) :
    let R := fun n : ℕ => 1 - ∑ d ∈ S, c d * ((n % d : ℕ) : ℝ) / d
    let M := (1 - ∑ d ∈ S, c d * ((d : ℝ) - 1) / (2*d)) ^ 2 +
      ∑ d ∈ S, ∑ e ∈ S, c d*c e*((d.gcd e : ℝ)^2-1)/(12*d*e)
    (∀ a L : ℕ, ∑ j ∈ Finset.range L, (R (a+j+1))^2 ≤ ((L : ℝ) + (D : ℝ)^2) * M) ∧
    ∀ H : ℕ, let E := fun j : ℕ => (R (H+j+1))^2 / ((((H+j : ℕ) : ℝ)+1)*(((H+j : ℕ) : ℝ)+2))
      let C := M * (1/(H+1 : ℝ) + (D : ℝ)^2/((H+1 : ℝ)*(H+2 : ℝ)))
      (∀ L : ℕ, ∑ j ∈ Finset.range L, E j ≤ C) ∧ Summable E ∧ (∑' j : ℕ, E j) ≤ C := by sorry
