-- Prove2me | Theorems.Thm_MellinStrip_line_L2_clm
-- name    : MellinStrip.line_L2_clm
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T06:47:55.537198+00:00
-- url     : https://prove2.me/theorems/640c1598-a661-4048-9aa8-8ca51b2295b9
-- title:
--   Polynomially weighted Fourier transform is continuous from $\mathcal S(\mathbb R)$ to $L^2$
-- statement:
--   Fix $a\in\mathbb R$ and $N\in\mathbb N$. The linear map
--   $$g\longmapsto\Bigl(y\mapsto(a+iy)^N\int_{\mathbb R}g(x)\,e^{iyx}\,dx\Bigr)$$
--   is a continuous linear map from the Schwartz space $\mathcal S(\mathbb R)$, with its Fréchet topology, into $L^2(\mathbb R,dy)$. In Lean, there is a continuous linear map $L\colon\mathcal S(\mathbb R)\to L^2(\mathbb R)$ whose value at $g$ is almost everywhere equal to the function above.
--
--   The reason: $(a+iy)^N\widehat g$ is the Fourier transform of $(a-\partial_x)^Ng$, which is again a Schwartz function. The Fourier transform and multiplication by polynomials are continuous on $\mathcal S(\mathbb R)$, and $\mathcal S(\mathbb R)\hookrightarrow L^2$ is continuous.
--
--   If $e^{ax}\psi=g$, then the function above is $y\mapsto(a+iy)^NM(\psi)(a+iy)$. Its $L^2$ norm is the seminorm defining the Schwartz–Bergman topology of $AS(\mathbb C_I)$ on the line $\operatorname{Re}s=a$. So this lemma is the continuity half of Proposition D.3.2.5.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Proposition D.3.2.5 (p. 802) and Lemma D.3.1.2 (pp. 799-800); continuity of M_I for the seminorms of Definition D.3.1.3. Standard Fourier analysis on Schwartz space.

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace MellinStrip

theorem line_L2_clm (a : ℝ) (N : ℕ) :
    ∃ L : SchwartzMap ℝ ℂ →L[ℂ] Lp ℂ 2 (volume : Measure ℝ), ∀ g : SchwartzMap ℝ ℂ,
      (L g : ℝ → ℂ) =ᵐ[volume] fun y : ℝ =>
        ((a : ℂ) + y * Complex.I) ^ N * ∫ x : ℝ, g x * Complex.exp (y * Complex.I * x) := by sorry

end MellinStrip
