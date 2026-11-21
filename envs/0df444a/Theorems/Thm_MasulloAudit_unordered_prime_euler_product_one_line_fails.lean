-- Prove2me | Theorems.Thm_MasulloAudit_unordered_prime_euler_product_one_line_fails
-- name    : MasulloAudit.unordered_prime_euler_product_one_line_fails
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:32:52.999397+00:00
-- url     : https://prove2.me/theorems/8d932df9-1e3a-44d9-80a1-543238d799f5
-- title:
--   The unordered prime Euler product of ζ has no limit on the nonreal one-line
-- statement:
--   At every w with Re(w)=1 and Im(w)≠0 there is no complex limit of the net of Euler products ∏_{p∈S}(1−p^(−w))⁻¹ as S ranges over finite sets of rational primes ordered by inclusion. The conclusion rules out zero as well as nonzero limits.
--   This tests a precise step of the proof of Masullo’s Proposition 3.4.2.1. Corollary B.7.2.5 gives the convergence of products over p≤N to ζ(w). Proposition 3.4.2.1 invokes it for the net over all finite sets of finite places. These two convergence assertions differ in the rational trivial-character case, already with no finite places excluded.
-- source:
--   A. M. Masullo, The Music of the Primes, proof of Proposition 3.4.2.1, p. 145, following (3.4.2.2), and Corollary B.7.2.5, p. 653. Frozen 20 November 2026 draft, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . Size-ordered convergence is verified at https://prove2.me/theorems/c1eb36e8-9290-4428-b237-91188f57ddc2 .

import Mathlib

theorem MasulloAudit.unordered_prime_euler_product_one_line_fails (w : ℂ) (hr : w.re=1) (hi : w.im≠0) :
    ¬Multipliable (fun p : Nat.Primes => (1-(p:ℂ)^(-w))⁻¹) := by sorry
