-- Prove2me | Theorems.Thm_MasulloRH_weighted_zero_summability
-- name    : MasulloRH.weighted_zero_summability
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-11-20T21:36:19.16536+00:00
-- url     : https://prove2.me/theorems/0ddc1d9a-5988-4c5e-be94-fbf74e18d3f2
-- title:
--   Classical analytic input — Weighted summability of zeta zeros
-- statement:
--   The family $m_\rho/(1+(\Im\rho)^2)$ is summable over the actual distinct nontrivial zeta zeros in every positive strip window. Multiplicities are actual analytic orders. This is a classical zero-counting input, not a consequence of RH.
--
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   Let $Z_α$ be the set of complex numbers $ρ$ such that $ζ(ρ)=0$, $0<Re(ρ)<1$, and $|Re(ρ)-1/2|<α$, where $ζ$ is the actual Riemann zeta function; each distinct location is an index. Write $m(ρ)$ for its natural-number analytic order at $ρ$: the local vanishing order when analytic and not identically zero nearby, with value zero if nonanalytic or identically zero nearby. For every real $α>0$, the real-valued family indexed by $Z_α$ whose value at $ρ$ is $m(ρ)/(1+Im(ρ)^2)$ is summable: its net of finite partial sums converges to some real number. There is no upper bound assumption on $α$; if $Z_α$ is empty the family is the empty summable family.
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

theorem weighted_zero_summability (α : ℝ) (hα : 0 < α) :
    Summable (zeroDecayWeight α) := by sorry

end MasulloRH
