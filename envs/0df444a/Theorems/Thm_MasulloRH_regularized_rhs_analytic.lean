-- Prove2me | Theorems.Thm_MasulloRH_regularized_rhs_analytic
-- name    : MasulloRH.regularized_rhs_analytic
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-11-20T21:36:16.586506+00:00
-- url     : https://prove2.me/theorems/0c25327b-0860-4561-94fb-13f11809b724
-- title:
--   §1.4.5 reconstruction — Holomorphy of the assembled trace expression
-- statement:
--   The explicitly defined $H_\alpha$ is analytic on $\{s:\Re s>1/2+\alpha,\ s\ne1\}$ for each $0<\alpha<1/2$. This reduction uses holomorphy of the real integral and spectral sum, plus the elementary rational polar terms and a constant.
--
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   For every real $\alpha$ with $0<\alpha<1/2$ and every complex number $s$ satisfying $\operatorname{Re}s>1/2+\alpha$ and $s\ne1$, the function $R_\alpha$ has a convergent complex power-series expansion on a neighborhood of $s$. Write $A(w)=\int_{(1,\infty)}(t^{1/2-w}-t^{-2})\sqrt t/(t^2-1)\,dt$, with additive real Lebesgue measure, real $t$ coerced to a complex number in both complex powers, and the real factor $\sqrt t/(t^2-1)$ coerced to a complex number. This is the totalized complex Bochner integral, which is zero if its integrand is not integrable. Let $Z_\alpha$ be the set of distinct complex numbers $\rho$ satisfying $\zeta(\rho)=0$, $0<\operatorname{Re}\rho<1$, and $|\operatorname{Re}\rho-1/2|<\alpha$, where $\zeta$ is the actual Riemann zeta function. Let $m(\rho)$ be its natural-number analytic order at $\rho$: the local vanishing order when it is analytic and not locally identically zero, and zero if it is not analytic or is locally identically zero. Put $S_\alpha(w)=\sum_{\rho\in Z_\alpha}m(\rho)((w-\rho)^{-1}-(5/2-\rho)^{-1})$, with natural multiplicities coerced to complex numbers. This is the unordered topological sum over distinct zero locations, including a possibly empty index set; as a totalized sum in $\mathbb C$, it is zero if the family is not summable. Put $P(w)=((w-1)^{-1}-(5/2-1)^{-1})+(w^{-1}-(5/2)^{-1})$, $L(w)=\zeta\prime(w)/\zeta(w)$, and $R_\alpha(w)=L(5/2)+A(w)-P(w)+S_\alpha(w)$. Here $\zeta\prime$ denotes the totalized complex derivative, equal to zero where the derivative does not exist, and complex division and inversion are totalized with $0^{-1}=0$, so in particular $L(w)=0$ at every zero of $\zeta$.
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

theorem regularized_rhs_analytic (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ (regularizedTraceRHS α) s := by sorry

end MasulloRH
