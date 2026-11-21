-- Prove2me | Theorems.Thm_MasulloRH_logDeriv_on_strip_complement
-- name    : MasulloRH.logDeriv_on_strip_complement
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-11-20T21:36:15.71778+00:00
-- url     : https://prove2.me/theorems/d50ef798-57ea-4306-a602-313bd21a9faa
-- title:
--   §1.4.5 reconstruction — Logarithmic-derivative holomorphy beyond each strip
-- statement:
--   For each $0<\alpha<1/2$, the actual logarithmic derivative of zeta is analytic at every $s$ with $\Re s>1/2+\alpha$ and $s\ne1$. Its reduction combines the initial identity, holomorphy of its explicit continuation, continuation of the derivative equation, and the local ODE lemma. Every point right of the critical line lies beyond one such positive strip.
--
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   For every real $\alpha$ with $0<\alpha<1/2$ and every complex number $s$ with $\operatorname{Re}s>1/2+\alpha$ and $s\ne1$, the function $w\mapsto\zeta\prime(w)/\zeta(w)$ has a convergent complex power-series expansion on a neighborhood of $s$. Here $\zeta$ is the actual Riemann zeta function, its prime denotes the totalized complex derivative (zero where the derivative does not exist), and the quotient is totalized using $0^{-1}=0$, including at zeros of $\zeta$. No nonvanishing assumption on $\zeta(s)$ is made.
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

theorem logDeriv_on_strip_complement (α : ℝ) (hα : 0 < α)
    (hαsmall : α < 1 / 2) (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ zetaLogDeriv s := by sorry

end MasulloRH
