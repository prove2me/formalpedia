-- Prove2me | Theorems.Thm_MasulloRH_regularized_spectral_domination
-- name    : MasulloRH.regularized_spectral_domination
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-11-20T21:36:18.964227+00:00
-- url     : https://prove2.me/theorems/3885a04c-8332-4022-8035-11d5bacaf1d2
-- title:
--   §1.4.3 reconstruction — Uniform spectral bound for the fixed cutoffs
-- statement:
--   For each fixed $0<\alpha<1/2$ and $\Re s>3/2$, there exists one positive constant independent of both cutoff index and zero such that the absolute cutoff spectral summand is bounded by that constant times $m_\rho/(1+(\Im\rho)^2)$. Pointwise cutoff convergence alone is not this bound. Its proof must establish uniform derivative estimates in log coordinates and perform integration by parts.
--
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   For each nonnegative integer $n$ (including $n=0$), set $N=n+1$, let $g(x)=0$ for $x≤0$ and $g(x)=e^{-1/x}$ for $x>0$, and set $H(x)=g(x)/(g(x)+g(1-x))$. Define $χ_n(t)=H(N log(t)-1)(1-H(log(t)/N-1))$ when $t>1$, and $χ_n(t)=0$ otherwise; define $f_{n,s}(t)=χ_n(t)(t^{1/2-s}-t^{-2})$ when $t>1$, and $f_{n,s}(t)=0$ otherwise, using complex powers of the positive real number $t$. Let $Z_α$ be the set of complex numbers $ρ$ such that $ζ(ρ)=0$, $0<Re(ρ)<1$, and $|Re(ρ)-1/2|<α$, where $ζ$ is the actual Riemann zeta function; each distinct location is an index. Write $m(ρ)$ for its natural-number analytic order at $ρ$: the local vanishing order when analytic and not identically zero nearby, with value zero if nonanalytic or identically zero nearby. Write $M(f,w)=∫_{0}^{∞}t^{w-1}f(t) dt$, with additive real Lebesgue measure and complex powers. For every real $α$ satisfying $0<α<1/2$ and every complex $s$ with $Re(s)>3/2$, there exists a real constant $C>0$ such that, simultaneously for every nonnegative integer $n$ and every $ρ∈Z_α$, $|m(ρ)M(f_{n,s},ρ-1/2)|≤C m(ρ)/(1+Im(ρ)^2)$. The constant may depend on $α$ and $s$, but is chosen before $n$ and $ρ$; if $Z_α$ is empty the universal bound is vacuous. Integrals are the totalized complex Bochner integrals (zero for a nonintegrable integrand); unordered sums are totalized sums (zero when the family is not summable).
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

theorem regularized_spectral_domination (α : ℝ) (hα : 0 < α)
    (hαsmall : α < 1 / 2) (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ρ : ZetaZerosInTraceStrip α),
      ‖zetaTraceTerm (regularizedTraceTest n s) α ρ‖ ≤ C * zeroDecayWeight α ρ := by sorry

end MasulloRH
