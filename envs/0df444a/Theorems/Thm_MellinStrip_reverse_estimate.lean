-- Prove2me | Theorems.Thm_MellinStrip_reverse_estimate
-- name    : MellinStrip.reverse_estimate
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T06:47:54.113174+00:00
-- url     : https://prove2.me/theorems/48d72863-9715-4a13-ac79-417a98cf94c6
-- title:
--   Schwartz seminorms of $e^{ax}\psi$ are controlled by $L^2$ norms of the Mellin transform on finitely many vertical lines
-- statement:
--   Let $I\subset\mathbb R$ be open, $a\in I$, and $k,n\in\mathbb N$. There are finitely many pairs $(b_j,N_j)$ with $b_j\in I$, and a constant $C$, such that the following holds. For every $\psi\colon\mathbb R\to\mathbb C$ for which every $g_b(x)=e^{bx}\psi(x)$ $(b\in I)$ is a Schwartz function,
--   $$\sup_{x\in\mathbb R}|x|^k\,\bigl\|D^n g_a(x)\bigr\|\ \le\ C\sum_j\Bigl\|\,y\mapsto(b_j+iy)^{N_j}\int_{\mathbb R}\psi(x)e^{(b_j+iy)x}\,dx\,\Bigr\|_{L^2(\mathbb R,dy)}.$$
--
--   In words, each Schwartz seminorm of $e^{ax}\psi$ is bounded by finitely many of the Schwartz–Bergman seminorms of the Mellin transform $M(\psi)$, evaluated on vertical lines inside $\mathbb C_I$.
--
--   **Proof idea.** By Plancherel, the $L^2$ norm on the line $\operatorname{Re}s=b$ of $s^NM(\psi)(s)$ equals $\sqrt{2\pi}\,\|e^{bx}\partial_x^N\psi\|_{L^2}$. The polynomial weight $|x|^k$ is absorbed by $e^{ax}|x|^k\le C_\delta(e^{(a-\delta)x}+e^{(a+\delta)x})$, with $a\pm\delta\in I$ since $I$ is open. Sup norms are bounded by $L^2$ norms of the function and its first derivative (one-dimensional Sobolev embedding). This gives continuity of the inverse map $M_I^{-1}$ in Proposition D.3.2.5, and also injectivity of $M_I$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Proposition D.3.2.5 (p. 802) and Lemma D.3.1.2 (pp. 799-800); continuity of the inverse of M_I.

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace MellinStrip

theorem reverse_estimate (I : Set ℝ) (hI : IsOpen I) (a : ℝ) (ha : a ∈ I) (k n : ℕ) :
    ∃ (S : Finset (ℝ × ℕ)) (C : ℝ), (∀ p ∈ S, p.1 ∈ I) ∧
      ∀ (ψ : ℝ → ℂ) (g : ℝ → SchwartzMap ℝ ℂ),
        (∀ b ∈ I, ∀ x : ℝ, g b x = (Real.exp (b * x) : ℂ) * ψ x) →
        SchwartzMap.seminorm ℂ k n (g a) ≤
          C * ∑ p ∈ S, (eLpNorm (fun y : ℝ => ((p.1 : ℂ) + y * Complex.I) ^ p.2 *
            ∫ x : ℝ, ψ x * Complex.exp (((p.1 : ℂ) + y * Complex.I) * x)) 2 volume).toReal := by sorry

end MellinStrip
