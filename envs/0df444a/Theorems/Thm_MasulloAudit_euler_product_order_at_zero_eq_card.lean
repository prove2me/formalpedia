-- Prove2me | Theorems.Thm_MasulloAudit_euler_product_order_at_zero_eq_card
-- name    : MasulloAudit.euler_product_order_at_zero_eq_card
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:05:25.206153+00:00
-- url     : https://prove2.me/theorems/2ade4db2-fbfc-47ef-a008-3f3e6cb4a1c6
-- title:
--   $\prod_{p\in S}(1-p^{-s})$ vanishes to order exactly $|S|$ at $s=0$
-- statement:
--   For a finite set $S$ of primes, the reciprocal finite Euler product of the Riemann zeta function
--
--   $$
--   E_S(s)=\prod_{p\in S}\bigl(1-p^{-s}\bigr)
--   $$
--
--   vanishes at $s=0$ to order exactly $|S|$:
--
--   $$
--   \operatorname{ord}_{s=0}E_S=|S|.
--   $$
--
--   Each factor $1-p^{-s}$ is entire and has a simple zero at $s=0$, with derivative $\log p\neq0$ there. Orders of vanishing add over finite products.
--
--   Equivalently, the finite Euler product $\prod_{p\in S}(1-p^{-s})^{-1}$ has a pole of order exactly $|S|$ at $s=0$. This is the "infinitely repeated pole" of finite Euler products that Masullo identifies in §1.7.3 (p. 37) as the obstruction to a trace formula at window width $0$. It is relevant to Proposition 11.2.0.1(2) (p. 484), whose closed-range assertion for $\mathrm{PV}_{S_0}$ assumes Sobolev degree $s\ge 2|S_0|$.
--
--   **Formalization Note.** The order of vanishing is Mathlib's `analyticOrderAt`, valued in `ℕ∞`, and $p^{-s}$ is complex exponentiation with a positive real base.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf: Proposition 11.2.0.1(2) (p. 484, hypothesis s ≥ 2|S_0|), Theorem 11.1.2.1 (p. 480, hypothesis s ≥ 2[F:Q] for all finite S_i) and its proof (p. 481); the 'infinitely repeated pole' of finite Euler products in §1.7.3 (p. 37).

import Mathlib

open Complex

namespace MasulloAudit

theorem euler_product_order_at_zero_eq_card (S : Finset Nat.Primes) :
    analyticOrderAt (fun s : ℂ => ∏ p ∈ S, (1 - ((p : ℕ) : ℂ) ^ (-s))) 0 = S.card := by sorry

end MasulloAudit
