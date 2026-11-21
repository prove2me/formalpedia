-- Prove2me | Theorems.Thm_MasulloGRH_sobolev_window_jet_integrable_iff
-- name    : MasulloGRH.sobolev_window_jet_integrable_iff
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-21T00:22:48.457554+00:00
-- url     : https://prove2.me/theorems/f7ee6f48-2eca-4410-baf6-8472a97b8705
-- title:
--   Windowed Sobolev jets: all interior orders and a strict boundary threshold
-- statement:
--   Let $m\in\mathbb N$, $s>1$, and $|b|\le\alpha$. Then $$\int_{\mathbb R}e^{2bx-2\alpha|x|}\frac{x^{2m}}{(1+x^2)^{s/2}}\,dx<\infty\quad\Longleftrightarrow\quad |b|<\alpha\ \text{or}\ 2m+1<s.$$ Thus every logarithmic jet order is integrable strictly inside the window. At either boundary, the strict scalar Sobolev threshold is necessary and sufficient; equality is excluded. The statement also covers the degenerate window $\alpha=0$.
--
--   This is the positive-real scalar integrability calculation for the windowed norm displayed in the proof of Proposition 10.2.2.2. Under $t=e^x$, its exponential factor is $t^{2b}/\max(t^{2\alpha},t^{-2\alpha})$ and $dx=dt/t$. It does not assert the Markushevich basis, the full spectral quotient identification, or uniform bounds on the biorthogonal functionals.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, pp. 446–447: Theorem 10.2.2.1 equations (10.2.2.4)–(10.2.2.6), and the displayed windowed norm in the proof of Proposition 10.2.2.2 on p. 447. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. This formalizes the scalar integral underlying the interior/boundary distinction and corrects the boundary equality case in the printed floor-plus-one count, consistently with the strict criterion of Proposition 9.1.2.5.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem MasulloGRH.sobolev_window_jet_integrable_iff (m : ℕ) (s α b : ℝ) (hs : 1 < s) (hb : |b| ≤ α) :
    Integrable (fun x : ℝ => Real.exp (2 * b * x - 2 * α * |x|) *
      (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) ↔
      |b| < α ∨ 2 * (m : ℝ) + 1 < s := by sorry
