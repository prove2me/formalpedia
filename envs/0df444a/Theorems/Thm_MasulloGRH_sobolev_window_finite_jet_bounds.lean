-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_window_finite_jet_bounds
-- name    : MasulloGRH.sobolev_window_finite_jet_bounds
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:29:08.203195+00:00
-- url     : https://prove2.me/theorems/06f128b5-1cad-4142-b298-09fc74ceeb57
-- title:
--   Uniform windowed jet bounds with a finite admissible-order cap
-- statement:
--   Let $M\in\mathbb N$, $\alpha\ge0$, and $s>2M+1$. There exists a constant $C>0$ such that, for every $0\le m\le M$ and $|b|\le\alpha$, $$C^{-1}\le\int_{\mathbb R}e^{2bx-2\alpha|x|}\frac{x^{2m}}{(1+x^2)^{s/2}}\,dx\le C.$$ Thus the squared weighted norms of this finite range of scalar jet orders lie in a common annulus, uniformly over the entire closed window, including its boundary. Oscillatory unit phases do not change these squared norms.
--
--   This is a sufficient-condition version of the scalar norm-bounding step in Proposition 10.2.2.2. The global cap $M$ and strict margin $s>2M+1$ are explicit additional hypotheses. The theorem does not establish those hypotheses for the source’s zeta-indexed family or bound its biorthogonal functionals.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, pp. 446–447, Proposition 10.2.2.2 and its displayed scalar norm. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This is an explicitly restricted sufficient-condition version of the scalar annulus estimate: a uniform finite order cap with s>2M+1 replaces the source’s spectral indexing assumptions. It is not the full proposition.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem MasulloGRH.sobolev_window_finite_jet_bounds (M : ℕ) (s α : ℝ) (hα : 0 ≤ α) (hs : 2 * (M : ℝ) + 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), m ≤ M → ∀ b : ℝ, |b| ≤ α →
      C⁻¹ ≤ ∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) *
        (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) ∧
      (∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) *
        (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) ≤ C := by sorry
