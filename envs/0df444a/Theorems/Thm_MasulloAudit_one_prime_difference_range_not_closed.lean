-- Prove2me | Theorems.Thm_MasulloAudit_one_prime_difference_range_not_closed
-- name    : MasulloAudit.one_prime_difference_range_not_closed
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:10:36.138184+00:00
-- url     : https://prove2.me/theorems/cf884b59-356f-4954-8b39-a80879a06abe
-- title:
--   The one-prime translation difference has nonclosed range in the weight of Proposition 11.2.0.1
-- statement:
--   For every $h>0$ the operator $D_hf(t)=f(t)-f(t+h)$ on the complex Hilbert space $L^2(\mathbb R,(1+t^2)\,dt)$ is bounded and injective, and its range is not closed.
--
--   In the rational trivial norm-one isotype, $t=\log|g|$, a single finite prime $p$ gives $h=\log p$. The weight above is the draft’s $s=2$ weight, which meets $s\ge 2|S_0|$ when $S_0=\{p\}$. This contradicts the closed-range assertion in Proposition 11.2.0.1(2) upon the identification with the weighted norm-coordinate space used in its proof. Reversing the sign of the shift gives the same range because translation is invertible.
-- source:
--   A. M. Masullo, The Music of the Primes, Nov. 20 draft, Proposition 11.2.0.1(2), (11.2.0.4), pp. 484–485. Its proof replaces the completed orbital space by the whole weighted space and the single-prime action by the translation difference. Theorem 11.1.2.1(1), p. 481, invokes this closed range. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib

open MeasureTheory Set Filter Topology

theorem MasulloAudit.one_prime_difference_range_not_closed (h : ℝ) (hh : 0<h) :
    let ν : Measure ℝ := volume.withDensity (fun t : ℝ => ENNReal.ofReal (1+t^2))
    ∃ D : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν,
      (∀ f : Lp ℂ 2 ν, (fun x => D f x)=ᵐ[ν] fun x => f x-f (x+h)) ∧
      Function.Injective D ∧ ¬IsClosed (Set.range D) := by sorry
