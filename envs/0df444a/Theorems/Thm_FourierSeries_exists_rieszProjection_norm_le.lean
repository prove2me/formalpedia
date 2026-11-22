-- Prove2me | Theorems.Thm_FourierSeries_exists_rieszProjection_norm_le
-- name    : FourierSeries.exists_rieszProjection_norm_le
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T19:14:17.128447+00:00
-- url     : https://prove2.me/theorems/1bc15900-ce3d-4199-8236-db87086e0738
-- title:
--   M. Riesz: the analytic projection $\sum c_ne_n\mapsto\sum_{n\ge0}c_ne_n$ of trigonometric polynomials is bounded in $L^p(\mathbb T)$, $1<p<\infty$
-- statement:
--   **M. Riesz's theorem: the analytic (Riesz) projection is bounded on $L^p(\mathbb T)$, $1<p<\infty$.** Let $T>0$, let $\mathbb T=\mathbb R/T\mathbb Z$ carry its normalized Haar measure, and let $e_n(x)=e^{2\pi inx/T}$ for $n\in\mathbb Z$. Let $1<p<\infty$. Then there is a constant $C$ such that for every finite set $S\subset\mathbb Z$ and all coefficients $c_n\in\mathbb C$
--
--   $$\Bigl\|\sum_{n\in S,\ n\ge0}c_n\,e_n\Bigr\|_{L^p(\mathbb T)}\;\le\;C\,\Bigl\|\sum_{n\in S}c_n\,e_n\Bigr\|_{L^p(\mathbb T)} .$$
--
--   In other words, the Riesz projection $P_+\colon\sum_n c_ne_n\mapsto\sum_{n\ge0}c_ne_n$, defined on trigonometric polynomials, extends to a bounded operator on $L^p(\mathbb T)$. Since $P_+f=\tfrac12\bigl(f+i\tilde f\bigr)+\tfrac12\widehat f(0)$, where $\tilde f=\sum_n(-i\,\operatorname{sgn} n)\,\widehat f(n)\,e_n$ is the conjugate function, this is equivalent to M. Riesz's theorem that conjugation is bounded on $L^p(\mathbb T)$ for $1<p<\infty$; the statement fails for $p=1$ and $p=\infty$.
--
--   This is the analytic input behind the $L^p$-norm convergence of Fourier series: from the identity $S_Nf=e_{-N}\,P_+(e_Nf)-e_{N+1}\,P_+(e_{-N-1}f)$ for the symmetric partial sums one gets $\|S_Nf\|_p\le2C\|f\|_p$ uniformly in $N$, which together with the density of trigonometric polynomials shows that the exponential system, in the order $0,1,-1,2,-2,\dots$, is a Schauder basis of $L^p(\mathbb T)$ (recalled by the source in §4.1.1).
--
--   **Formalization Note.** `fourierLp p n` is the class of $e_n$ in Mathlib's `Lp ℂ p haarAddCircle`; a trigonometric polynomial is given by a finite set `s : Finset ℤ` and an arbitrary coefficient function `c : ℤ → ℂ` (only its values on `s` matter), and the projected polynomial is the filtered sum over `n ∈ s` with `0 ≤ n`. The constant may depend on $T$ and $p$. The instance `[Fact (1 ≤ p)]` is required for `Lp` to be a normed space and is implied by `1 < p`; `p ≠ ∞` excludes $p=\infty$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 157, §4.1.1 (the exponential system in $L^p(\mathbb T)$, recalled from [Katzn, Ch. II, §1.5]); auxiliary lemma for the proof of SchauderBasis.exists_schauderBasis_Lp_fourier; classical reference: M. Riesz, Sur les fonctions conjuguées, Math. Z. 27 (1928), 218–244; Y. Katznelson, An Introduction to Harmonic Analysis, 3rd ed., Cambridge University Press, 2012, Ch. III (the conjugate function)

import Mathlib

open MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace FourierSeries

theorem exists_rieszProjection_norm_le (T : ℝ) [Fact (0 < T)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hp' : p ≠ ∞) :
    ∃ C : ℝ, ∀ (s : Finset ℤ) (c : ℤ → ℂ),
      ‖∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n‖ ≤
        C * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖ := by sorry

end FourierSeries
