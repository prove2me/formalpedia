-- Prove2me | Theorems.Thm_NymanBeurling_prime_coefficient_sq_le_certificate
-- name    : NymanBeurling.prime_coefficient_sq_le_certificate
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:44:50.833024+00:00
-- url     : https://prove2.me/theorems/9a53cb05-4004-4a4e-8b81-4200b8e7a35c
-- title:
--   Prime coefficients forced by finite Nyman–Beurling remainder certificates
-- statement:
--   For every finitely supported rational coefficient vector $c$, cutoff $H\ge0$ and prime $p$, the exact rational cost $C_H(c)$ from the finite remainder criterion bounds the deviation of the coefficient at denominator $p$:
--   $$|1-c_{p-2}|^2\le K_p C_H(c),\qquad K_2=14,\quad K_p=2p^2+2\ (p\ge3).$$
--   In particular, if $C_H(c)<1/(J+1)$ and $J+1\ge K_p$, denominator $p$ must be present, regardless of the larger denominators used. Any sequence of certificate costs tending to zero forces each fixed prime coefficient to approach one.
-- source:
--   Elementary obstruction for the finite rational Nyman–Beurling remainder certificate https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339, based on the jump at a prime of the discrete remainder (n mod d)/d and weighted Cauchy–Schwarz.

import Mathlib

set_option autoImplicit false

theorem NymanBeurling.prime_coefficient_sq_le_certificate (c : ℕ →₀ ℚ) (H p : ℕ) (hp : p.Prime) :
    (1 - c (p-2))^2 ≤ (if p=2 then 14 else 2*(p:ℚ)^2+2) *
      ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) := by sorry
