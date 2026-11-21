-- Prove2me | Theorems.Thm_MasulloRH_regularized_spectral_analytic
-- name    : MasulloRH.regularized_spectral_analytic
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-11-20T21:36:15.910523+00:00
-- url     : https://prove2.me/theorems/db89b743-04b7-4c9a-91cd-7d3c19740ed6
-- title:
--   §1.4.3 reconstruction — Holomorphy of the zero-resolvent sum
-- statement:
--   For $0<\alpha<1/2$ and $\Re s>1/2+\alpha$, the zero-resolvent family is summable and its sum is complex analytic at $s$. The actual zero set, full multiplicities and strict strip bounds are used. A proof needs locally uniform control, not only pointwise convergence.
--
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   For every real $\alpha$ with $0<\alpha<1/2$ and every complex number $s$ with $\operatorname{Re}s>1/2+\alpha$, the family $\bigl(m(\rho)((s-\rho)^{-1}-(5/2-\rho)^{-1})\bigr)_{\rho\in Z_\alpha}$ is summable in $\mathbb C$, and the function $S_\alpha$ has a convergent complex power-series expansion on a neighborhood of $s$. Let $Z_\alpha$ be the set of distinct complex numbers $\rho$ satisfying $\zeta(\rho)=0$, $0<\operatorname{Re}\rho<1$, and $|\operatorname{Re}\rho-1/2|<\alpha$, where $\zeta$ is the actual Riemann zeta function. Let $m(\rho)$ be its natural-number analytic order at $\rho$: the local vanishing order when it is analytic and not locally identically zero, and zero if it is not analytic or is locally identically zero. Put $S_\alpha(w)=\sum_{\rho\in Z_\alpha}m(\rho)((w-\rho)^{-1}-(5/2-\rho)^{-1})$, with natural multiplicities coerced to complex numbers. This is the unordered topological sum over distinct zero locations, including a possibly empty index set; as a totalized sum in $\mathbb C$, it is zero if the family is not summable. All inverses are complex and totalized with $0^{-1}=0$.
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

theorem regularized_spectral_analytic (α : ℝ) (hα : 0 < α)
    (hαsmall : α < 1 / 2) (s : ℂ) (hs : 1 / 2 + α < s.re) :
    Summable (zeroResolventTerm α s) ∧ AnalyticAt ℂ (regularizedSpectral α) s := by sorry

end MasulloRH
