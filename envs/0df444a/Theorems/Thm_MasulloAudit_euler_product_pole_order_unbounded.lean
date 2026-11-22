-- Prove2me | Theorems.Thm_MasulloAudit_euler_product_pole_order_unbounded
-- name    : MasulloAudit.euler_product_pole_order_unbounded
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:05:20.803143+00:00
-- url     : https://prove2.me/theorems/04bd9bdf-89f6-497c-9323-50cd8156155d
-- title:
--   Pole orders of finite Euler products of $\zeta$ at $s=0$ are unbounded
-- statement:
--   For every natural number $N$ there is a finite set $S$ of primes such that the finite Euler product
--
--   $$
--   \zeta_S(s)=\prod_{p\in S}\bigl(1-p^{-s}\bigr)^{-1}
--   $$
--
--   has a pole of order greater than $N$ at $s=0$. In other words, the pole orders of the finite Euler products of $\zeta$ at the point $s=0$ are unbounded as $S$ grows. (In fact the order is exactly $|S|$.)
--
--   This is the ζ-case of the "infinitely repeated pole" in §1.7.3 (p. 37) of Masullo's draft. Proposition 11.2.0.1(2) (p. 484) requires Sobolev degree $s\ge 2|S_0|$ for $\mathrm{PV}_{S_0}$ to have closed range. Theorem 11.1.2.1 (p. 480) assumes only $s\ge 2[F:\mathbf Q]$, yet its proof (p. 481) applies Proposition 11.2.0.1 to arbitrary finite sets $S_i$. For $F=\mathbf Q$ no fixed $s$ meets $s\ge 2|S_i|$ for all $S_i$, and the unbounded pole order at $s=0$ is a natural source of a requirement that grows with $|S_i|$. The draft does not state the reason for the hypothesis $s\ge2|S_0|$.
--
--   **Formalization Note.** The order is Mathlib's `meromorphicOrderAt` (valued in `WithTop ℤ`), where a pole of order $k$ means order $-k$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf: Proposition 11.2.0.1(2) (p. 484, hypothesis s ≥ 2|S_0|), Theorem 11.1.2.1 (p. 480, hypothesis s ≥ 2[F:Q] for all finite S_i) and its proof (p. 481); the 'infinitely repeated pole' of finite Euler products in §1.7.3 (p. 37).

import Mathlib

open Complex

namespace MasulloAudit

theorem euler_product_pole_order_unbounded (N : ℕ) : ∃ S : Finset Nat.Primes,
    meromorphicOrderAt (fun s : ℂ => ∏ p ∈ S, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹) 0 < -(N : ℤ) := by sorry

end MasulloAudit
