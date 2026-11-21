-- Prove2me | Theorems.Thm_MasulloRH_regularized_prime_limit
-- name    : MasulloRH.regularized_prime_limit
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-11-20T21:36:20.299085+00:00
-- url     : https://prove2.me/theorems/5bbf95ab-e29e-4476-864d-1769483d094c
-- title:
--   §1.4.4 reconstruction — Signed prime-series limit
-- statement:
--   For $\Re s>3/2$, the cutoff prime-power side tends to $-\zeta^{\prime}(s)/\zeta(s)+\zeta^{\prime}(5/2)/\zeta(5/2)$. The minus sign is required by the actual Euler product. The source overview prints the opposite sign.
--
--   **Reconstruction status.** These nodes make precise a possible repair of Masullo §§1.4.2–1.4.5, pp.28–30. They are not verbatim additional theorems found in the draft. The unsubtracted step-family in the overview produces a logarithmically divergent real-place integral at one. This reconstruction subtracts a fixed base exponent, uses a fixed smooth cutoff construction, and keeps the Euler-product sign explicit. All unresolved analytic statements remain open.
--
--   The complex parameter $s$ is the unshifted zeta argument. The cutoff test on $t>1$ is $\kappa_n(t)(t^{1/2-s}-t^{-2})$ and is zero on $t\le1$. Put $N=n+1$ and $\kappa_n(t)=\theta(N\log t-1)(1-\theta(\log t/N-1))$, where $\theta$ is Mathlib's smoothTransition. The zero sum ranges over actual zeros with $0<\Re\rho<1$ and $|\Re\rho-1/2|<\alpha$, with full analytic multiplicity and no height cutoff. Definitions contain no asserted trace identity or holomorphy conclusion.
--
--
--   **Independent blind read-back:**
--
--   For each nonnegative integer $n$ (including $n=0$), set $N=n+1$, let $g(x)=0$ for $x≤0$ and $g(x)=e^{-1/x}$ for $x>0$, and set $H(x)=g(x)/(g(x)+g(1-x))$. Define $χ_n(t)=H(N log(t)-1)(1-H(log(t)/N-1))$ when $t>1$, and $χ_n(t)=0$ otherwise; define $f_{n,s}(t)=χ_n(t)(t^{1/2-s}-t^{-2})$ when $t>1$, and $f_{n,s}(t)=0$ otherwise, using complex powers of the positive real number $t$. Let $L(z)=ζ′(z)/ζ(z)$, where the derivative is the totalized complex derivative (zero where differentiability fails), and complex division by zero is zero. For every complex $s$ with $Re(s)>3/2$, the sequence of unordered sums over all positive natural primes $p$ and nonnegative integers $k$, $Σ_{(p,k)} (log(p)/√(p^{k+1}))(f_{n,s}(p^{k+1})+f_{n,s}((p^{k+1})^{-1}))$, converges in $ℂ$ as $n→∞$ to $-L(s)+L(5/2)$. The exponent $k+1$ includes every strictly positive integer. Integrals are the totalized complex Bochner integrals (zero for a nonintegrable integrand); unordered sums are totalized sums (zero when the family is not summable).
-- source:
--   Reconstruction of Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, §§1.4.2–1.4.5, pp.28–30; Theorem 12.5.1.1, pp.519–520. Analytic continuation and local derivative-equation steps use standard complex analysis. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH

theorem regularized_prime_limit (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    Tendsto (fun n : ℕ => cutoffPrime n s) atTop
      (𝓝 (-zetaLogDeriv s + zetaLogDeriv (5 / 2))) := by sorry

end MasulloRH
