-- Prove2me | Theorems.Thm_MellinStrip_surjective
-- name    : MellinStrip.surjective
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T06:47:54.531935+00:00
-- url     : https://prove2.me/theorems/52e6b63b-846d-4107-bff8-44cdd43ba314
-- title:
--   Paley–Wiener on a vertical strip: uniformly Schwartz holomorphic functions are Mellin transforms
-- statement:
--   Let $I\subset\mathbb R$ be an open interval (open and order-connected; possibly empty or unbounded). Let $F$ be holomorphic on the strip $\mathbb C_I=\{s:\operatorname{Re}s\in I\}$ and uniformly Schwartz on its vertical substrips of bounded width. That is, for every compact $[a,b]\subset I$ and every $N\ge0$, $s^NF(s)$ is bounded on $\{a\le\operatorname{Re}s\le b\}$.
--
--   Then there is a function $\psi\colon\mathbb R\to\mathbb C$ such that $x\mapsto e^{ax}\psi(x)$ is a Schwartz function for every $a\in I$, and
--   $$\int_{\mathbb R}\psi(x)\,e^{sx}\,dx=F(s)\qquad(\operatorname{Re}s\in I).$$
--   In the coordinate $t=e^x$, $F$ is the Mellin transform of $\phi(t)=\psi(\log t)\in\mathcal S_I(\mathbb R_{>0})$.
--
--   **Proof idea.** For $a\in I$ put $\psi(x)=\frac1{2\pi}\int_{\mathbb R}F(a+iy)e^{-(a+iy)x}\,dy$. Cauchy's theorem on rectangles, together with the uniform decay, shows that this does not depend on $a\in I$; this is where the order-connectedness of $I$ is used. Cauchy estimates on a slightly wider substrip show that $y\mapsto F(a+iy)$ is a Schwartz function. Hence $e^{ax}\psi$, an inverse Fourier transform of it, is Schwartz, and Fourier inversion gives the Mellin identity on every line. This is the surjectivity of $M_I$ in Proposition D.3.2.5.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Proposition D.3.2.5 (p. 802) and Lemma D.3.1.2 (pp. 799-800); surjectivity of M_I (Paley-Wiener theorem for vertical strips).

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace MellinStrip

theorem surjective (I : Set ℝ) (hI : IsOpen I) (hI' : I.OrdConnected) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re ∈ I})
    (hbd : ∀ a b : ℝ, Set.Icc a b ⊆ I → ∀ N : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖s ^ N * F s‖ ≤ C) :
    ∃ ψ : ℝ → ℂ, (∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
        g x = (Real.exp (a * x) : ℂ) * ψ x) ∧
      ∀ s : ℂ, s.re ∈ I → ∫ x : ℝ, ψ x * Complex.exp (s * x) = F s := by sorry

end MellinStrip
