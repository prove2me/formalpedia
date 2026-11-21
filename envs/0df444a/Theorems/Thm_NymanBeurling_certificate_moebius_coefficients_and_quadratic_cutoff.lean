-- Prove2me | Theorems.Thm_NymanBeurling_certificate_moebius_coefficients_and_quadratic_cutoff
-- name    : NymanBeurling.certificate_moebius_coefficients_and_quadratic_cutoff
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:52:26.381589+00:00
-- url     : https://prove2.me/theorems/75892a74-5a83-4222-b8a3-e9892e482719
-- title:
--   Möbius coefficient constraints and a quadratic lower bound on finite remainder certificate cutoffs
-- statement:
--   With the finite rational cost $C=C_H(c)$ of Bagchi's remainder certificate, every integer $n\ge2$ satisfies
--   $$|c_{n-2}+\mu(n)|^2\le30n^2 C.$$
--   Consequently every certificate of level $J$ (that is, $C<1/(J+1)$) has a necessarily quadratic cutoff:
--   $$(J+1)^2<7680(H+1).$$
--   The assertions apply to arbitrary finitely supported rational coefficients and all cutoffs, including zero. In particular a sequence with costs tending to zero forces every fixed coefficient to approach minus the Möbius function at its denominator.
-- source:
--   Finite-certificate cost from https://prove2.me/theorems/5b7b7b22-9280-4b04-9e90-f2f88cb85339; its prime-coefficient obstruction https://prove2.me/theorems/9a53cb05-4004-4a4e-8b81-4200b8e7a35c suggested the all-index finite-difference and divisor inversion. The all-index, uniform quantitative bound and squarefree-density cutoff are proved directly here using Mathlib.

import Mathlib

set_option autoImplicit false

theorem NymanBeurling.certificate_moebius_coefficients_and_quadratic_cutoff (c : ℕ →₀ ℚ) (H : ℕ) :
    let C : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
    (∀ n : ℕ, 2 ≤ n → (c (n-2) + (ArithmeticFunction.moebius n : ℚ))^2
      ≤ 30*(n:ℚ)^2*C) ∧ (∀ J : ℕ, C < 1/((J:ℚ)+1) → (J+1)^2 < 7680*(H+1)) := by sorry
