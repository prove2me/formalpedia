-- Prove2me | Theorems.Thm_MellinStrip_expDecay_strip
-- name    : MellinStrip.expDecay_strip
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T06:47:55.265043+00:00
-- url     : https://prove2.me/theorems/0a11a885-cf64-4254-a4ea-6434c93e2e76
-- title:
--   Mellin transforms of functions with exponential decay are holomorphic and uniformly Schwartz on vertical strips
-- statement:
--   Let $I\subset\mathbb R$ be open and let $\psi\colon\mathbb R\to\mathbb C$ be such that, for every $a\in I$, the function $x\mapsto e^{ax}\psi(x)$ is a Schwartz function. Put
--   $$F(s)=\int_{\mathbb R}\psi(x)\,e^{sx}\,dx .$$
--   In the coordinate $t=e^x$ this is the Mellin transform $\int_0^\infty\phi(t)t^s\,dt/t$ of $\phi(t)=\psi(\log t)$. Then:
--
--   1. for every $s$ with $\operatorname{Re}s\in I$ the integrand $x\mapsto\psi(x)e^{sx}$ is integrable;
--   2. $F$ is holomorphic on the strip $\mathbb C_I=\{s:\operatorname{Re}s\in I\}$;
--   3. $F$ is uniformly Schwartz on vertical strips of bounded width. For every compact interval $[a,b]\subset I$ and every $N\ge0$ there is $C$ such that
--   $$|s^N F(s)|\le C\qquad(a\le\operatorname{Re}s\le b).$$
--
--   Item 3 follows from integration by parts, $s^NF(s)=\int(-\partial_x)^N\psi(x)\,e^{sx}\,dx$, together with $e^{\sigma x}\le e^{ax}+e^{bx}$ for $\sigma\in[a,b]$. This is the forward half of Proposition D.3.2.5 of the source: the Mellin transform maps $\mathcal S_I(\mathbb R_{>0})$ into $\mathcal S(\mathbb C_I)$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Proposition D.3.2.5 (p. 802) and Lemma D.3.1.2 (pp. 799-800); forward direction (the Mellin integral converges and lies in S(C_I)). Classical Fourier-Laplace/Paley-Wiener theory.

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace MellinStrip

theorem expDecay_strip (I : Set ℝ) (hI : IsOpen I) (ψ : ℝ → ℂ)
    (hψ : ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ, g x = (Real.exp (a * x) : ℂ) * ψ x) :
    (∀ s : ℂ, s.re ∈ I → Integrable (fun x : ℝ => ψ x * Complex.exp (s * x))) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∫ x : ℝ, ψ x * Complex.exp (s * x)) {s : ℂ | s.re ∈ I} ∧
    ∀ a b : ℝ, Set.Icc a b ⊆ I → ∀ N : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖s ^ N * ∫ x : ℝ, ψ x * Complex.exp (s * x)‖ ≤ C := by sorry

end MellinStrip
