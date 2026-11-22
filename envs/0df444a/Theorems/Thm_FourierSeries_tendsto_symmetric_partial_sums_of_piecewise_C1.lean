-- Prove2me | Theorems.Thm_FourierSeries_tendsto_symmetric_partial_sums_of_piecewise_C1
-- name    : FourierSeries.tendsto_symmetric_partial_sums_of_piecewise_C1
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:39.23323+00:00
-- url     : https://prove2.me/theorems/05c32559-a5d0-417e-bb95-748da9c7afbf
-- title:
--   Dirichlet's theorem: the Fourier series of a periodic piecewise $C^1$ function converges at every point to $\tfrac12\big(f(x^-)+f(x^+)\big)$
-- statement:
--   **Dirichlet's theorem on the pointwise convergence of Fourier series** (piecewise $C^1$ functions).
--
--   Let $T>0$ and let $f\colon\mathbb R\to\mathbb C$ be a $T$-periodic function which is *piecewise $C^1$* in the following sense: there is a finite set $S\subset\mathbb R$ such that
--
--   1. at every point $x\notin S+T\mathbb Z$ the function $f$ is differentiable and its derivative $f'$ is continuous at $x$;
--   2. at every point $x\in\mathbb R$ the one-sided limits $f(x^\pm)=\lim_{u\to x^\pm}f(u)$ exist in $\mathbb C$;
--   3. at every point $x\in\mathbb R$ the one-sided limits $f'(x^\pm)=\lim_{u\to x^\pm}f'(u)$ exist in $\mathbb C$.
--
--   (Conditions 2 and 3 only have content at the points of $S+T\mathbb Z$.) Let
--   $$a_n=\frac1T\int_0^T f(t)\,e^{-2\pi i n t/T}\,dt\qquad(n\in\mathbb Z)$$
--   be the Fourier coefficients of $f$. Then for every $x\in\mathbb R$ the symmetric partial sums of the Fourier series of $f$ converge at $x$, and
--   $$\lim_{N\to\infty}\ \sum_{|n|\le N}a_n\,e^{2\pi i n x/T}=\frac{f(x^-)+f(x^+)}{2}.$$
--   In particular the Fourier series converges to $f(x)$ at every point $x$ at which $f$ is continuous.
--
--   This is the classical convergence theorem of Dirichlet for piecewise smooth functions: no summability of the coefficients is required, and at a jump the series converges to the midpoint of the jump. The values of $f$ at the exceptional points play no role. The source applies it, with $T=1$, to the periodization $\alpha(x)=\sum_{m\in\mathbb Z}\phi_0(e^{x+m})$ of a function with finitely many jump singularities, in order to prove the Poisson summation formula with jump singularities (Proposition B.4.1.2).
--
--   **Formalization Note.** The exceptional set is given by a `Finset ℝ` `S`, and "$x\notin S+T\mathbb Z$" is written `∀ n : ℤ, x + n * T ∉ S`. `deriv f` is Mathlib's derivative, which is $0$ where $f$ is not differentiable; this can only happen on the closed discrete set $S+T\mathbb Z$, so the one-sided limits of `deriv f` are those of $f'$. The conclusion is stated for arbitrary `l`, `r` with `f → l` along `𝓝[<] x` and `f → r` along `𝓝[>] x`. The Fourier coefficients and the exponentials are written out explicitly (rather than through `fourierCoeffOn`) so that the normalization is visible; the integral is an interval integral for Lebesgue measure ($f$ is bounded and continuous off a finite subset of $[0,T]$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 609, proof of Proposition B.4.1.2, eqs. (B.4.1.11)-(B.4.1.13); classical reference: G. B. Folland, Fourier Analysis and Applications, Wadsworth and Brooks/Cole Advanced Books and Software, 1992, §2.2, Theorem 2.1, p. 35 (as cited by the paper)

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace FourierSeries

theorem tendsto_symmetric_partial_sums_of_piecewise_C1
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hper : Function.Periodic f T)
    (S : Finset ℝ)
    (hC1 : ∀ x : ℝ, (∀ n : ℤ, x + n * T ∉ S) →
      DifferentiableAt ℝ f x ∧ ContinuousAt (deriv f) x)
    (hlim : ∀ x : ℝ, ∃ l r : ℂ, Tendsto f (𝓝[<] x) (𝓝 l) ∧ Tendsto f (𝓝[>] x) (𝓝 r))
    (hlim' : ∀ x : ℝ, ∃ l r : ℂ,
      Tendsto (deriv f) (𝓝[<] x) (𝓝 l) ∧ Tendsto (deriv f) (𝓝[>] x) (𝓝 r))
    (x : ℝ) (l r : ℂ) (hl : Tendsto f (𝓝[<] x) (𝓝 l)) (hr : Tendsto f (𝓝[>] x) (𝓝 r)) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (((1 / T : ℝ) : ℂ) *
            ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(2 * π * Complex.I * n * t / T))) *
          Complex.exp (2 * π * Complex.I * n * x / T))
      atTop (𝓝 ((l + r) / 2)) := by sorry

end FourierSeries
