-- Prove2me | Theorems.Thm_MasulloRH_regularized_arch_analytic
-- name    : MasulloRH.regularized_arch_analytic
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-11-20T21:36:15.293742+00:00
-- url     : https://prove2.me/theorems/f21415fb-cdb9-45a8-a33d-cde0db41db81
-- title:
--   §1.4.3 reconstruction — Holomorphy of the regularized real-place integral
-- statement:
--   The actual integral $A(s)=\int_1^\infty(t^{1/2-s}-t^{-2})\sqrt t/(t^2-1)\,dt$ is complex analytic at every point with $\Re s>1/2$. A proof must justify integration in the complex parameter and endpoint bounds.
--
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   For every complex number $s$ with $\operatorname{Re}s>1/2$, the function $A$ has a convergent complex power-series expansion on a neighborhood of $s$. Write $A(w)=\int_{(1,\infty)}(t^{1/2-w}-t^{-2})\sqrt t/(t^2-1)\,dt$, with additive real Lebesgue measure, real $t$ coerced to a complex number in both complex powers, and the real factor $\sqrt t/(t^2-1)$ coerced to a complex number. This is the totalized complex Bochner integral, which is zero if its integrand is not integrable.
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

theorem regularized_arch_analytic (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ regularizedArch s := by sorry

end MasulloRH
