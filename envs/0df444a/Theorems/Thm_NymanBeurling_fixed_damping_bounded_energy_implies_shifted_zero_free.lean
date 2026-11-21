-- Prove2me | Theorems.Thm_NymanBeurling_fixed_damping_bounded_energy_implies_shifted_zero_free
-- name    : NymanBeurling.fixed_damping_bounded_energy_implies_shifted_zero_free
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:29:12.181745+00:00
-- url     : https://prove2.me/theorems/baa66214-985e-45bb-8cca-c47070b7cd0c
-- title:
--   Bounded Möbius energies at fixed damping imply a shifted zero-free half-plane
-- statement:
--   Fix $\varepsilon>0$. Write
--   $$R_{N,\varepsilon}(m)=1+\sum_{d=2}^{N+1}\frac{\mu(d)}{d^\varepsilon}\frac{m\bmod d}{d}.$$
--   Suppose the weighted prefix energies
--   $$\sum_{m=1}^H\frac{R_{N,\varepsilon}(m)^2}{m(m+1)}$$
--   are bounded uniformly in the denominator cutoff $N$ and the coordinate cutoff $H$. Then $\zeta(w)\ne0$ for $\Re w>1/2+\varepsilon$, with the pole $w=1$ excluded. This is a converse zero-free implication for the fixed-damping condition.
-- source:
--   A converse to the fixed-damping convergence frontier https://prove2.me/theorems/b5d23ede-9bcc-4d2a-9c23-84182e886efc. The discrete Hilbert-space Mellin pairing is from B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), pp. 137–146, https://arxiv.org/abs/math/0607733. The formalized finite Mellin inequality follows NymanBeurling.finite_remainder_zero_obstruction (Prove2Me submission 657705dd).

import Mathlib
import Definitions.Def_NymanBeurling_DampedResidualLimits

open NymanBeurling
open scoped BigOperators

theorem NymanBeurling.fixed_damping_bounded_energy_implies_shifted_zero_free
    (ε : ℝ) (hε : 0 < ε)
    (hB : ∃ B : ℝ, ∀ N H : ℕ, (∑ n ∈ Finset.range H,
      (dampedResidualFinite N ε (n+1)) ^ 2 / ((n+1 : ℝ) * (n+2 : ℝ))) ≤ B)
    (w : ℂ) (hw : 1/2 + ε < w.re) (h1 : w ≠ 1) :
    riemannZeta w ≠ 0 := by sorry
