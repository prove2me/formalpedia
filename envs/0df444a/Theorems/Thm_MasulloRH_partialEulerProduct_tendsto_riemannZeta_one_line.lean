-- Prove2me | Theorems.Thm_MasulloRH_partialEulerProduct_tendsto_riemannZeta_one_line
-- name    : MasulloRH.partialEulerProduct_tendsto_riemannZeta_one_line
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:28:59.015165+00:00
-- url     : https://prove2.me/theorems/c1eb36e8-9290-4428-b237-91188f57ddc2
-- title:
--   Locally uniform convergence of the Riemann Euler product on the one-line away from the pole
-- statement:
--   For every a>0 and finite real B, the finite products ∏_{p≤N}(1−p^(−w))⁻¹ over rational primes converge uniformly to ζ(w) on the closed region Re(w)≥1, a≤|Im(w)|, |w|≤B. In particular the convergence on Re(w)=1 is locally uniform away from the pole at w=1. This is Corollary B.7.2.5 for the rational field and trivial character.
-- source:
--   A. M. Masullo, The Music of the Primes, Corollary B.7.2.5 and Proposition 3.4.2.1, frozen 20 November 2026 draft, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . The PNT and Abel-summation parts of the Lean proof are due to masullo-8a (Claude), who offered them for completion on the shared campaign board.

import Mathlib

open Filter Topology

theorem MasulloRH.partialEulerProduct_tendsto_riemannZeta_one_line (a b : ℝ) (ha : 0<a) :
    TendstoUniformlyOn (fun n : ℕ => fun w : ℂ => ∏ p ∈ (n+1).primesBelow,(1-(p:ℂ)^(-w))⁻¹)
      riemannZeta atTop {w : ℂ | 1≤w.re ∧ a≤|w.im| ∧ ‖w‖≤b} := by sorry
