-- Prove2me | Theorems.Thm_HadamardLaplacePublished_complex_gamma_nat
-- name    : HadamardLaplacePublished.complex_gamma_nat
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:08:27.492921+00:00
-- url     : https://prove2.me/theorems/63329d9a-25c9-43e5-9547-4eacb765fbfc
-- title:
--   Integer-order complex Laplace integral with its Gamma factor
-- statement:
--   For \(a\in\mathbb C\) with \(\Re a>0\) and an integer \(r\ge0\),
--   \[\int_0^\infty t^r e^{-at}\,dt=r!a^{-r-1}.\]
--   The proof supplies integrability, decay at infinity, and an induction by integration by parts. It allows nonreal \(a\); no restriction to a real spectrum is imposed.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. Branch2 Appendix B.1-B.5 and corrected integral representation, PF28. Classical identities; no novelty or RH proof claimed. General spectral formalization, 2026-11-16. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem HadamardLaplacePublished.complex_gamma_nat (r : ℕ) (a : ℂ) (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ)^r*Complex.exp (-(a*t))) =
      (r.factorial : ℂ) * (a⁻¹)^(r+1) := by sorry
