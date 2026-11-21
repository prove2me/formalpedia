-- Prove2me | Theorems.Thm_NymanBeurling_finite_remainder_certificates_through_42
-- name    : NymanBeurling.finite_remainder_certificates_through_42
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:48:29.296745+00:00
-- url     : https://prove2.me/theorems/ed644939-4ab2-4240-9464-c2c11589f785
-- title:
--   An explicit Nyman–Beurling remainder certificate for every $J\le 42$
-- statement:
--   For a finitely supported rational vector $c$, define its residual at a positive integer $m$ by
--   $$e_c(m)=1-\sum_{d\ge2}c_{d-2}\frac{m\bmod d}{d}.$$
--   At an integer cutoff $H\ge0$, its certificate cost is
--   $$C_H(c)=\sum_{m=1}^H\frac{e_c(m)^2}{m(m+1)}+\frac{(1+\sum_k|c_k|)^2}{H+1}.$$
--   For every integer $0\le J\le42$, there exist $c$ and $H$ with $C_H(c)<1/(J+1)$. One pair works throughout this range. Take $H=262143$ and let $8c_{d-2}$ on the respective denominators $d=2,3,4,5,6,7,10,11$ equal $7,7,1,5,-3,4,-1,3$. All other entries vanish.
-- source:
--   Explicit finite instance of NymanBeurling.arbitrarily_small_remainder_certificates, https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339 . The coefficients were selected by finite numerical minimization and the submitted certificate is checked using exact rational and integer arithmetic.

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

theorem NymanBeurling.finite_remainder_certificates_through_42 (J : ℕ) (hJ : J ≤ 42) :
    ∃ (c : ℕ →₀ ℚ) (H : ℕ), ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1/(J+1 : ℚ) := by sorry
