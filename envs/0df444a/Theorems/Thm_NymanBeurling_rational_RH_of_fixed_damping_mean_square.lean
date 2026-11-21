-- Prove2me | Theorems.Thm_NymanBeurling_rational_RH_of_fixed_damping_mean_square
-- name    : NymanBeurling.rational_RH_of_fixed_damping_mean_square
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:30:24.202171+00:00
-- url     : https://prove2.me/theorems/e21d948c-777a-4b4b-b486-2963b6b6fd15
-- title:
--   The fixed-damping mean-square frontier implies the rational Riemann hypothesis
-- statement:
--   For every fixed damping $0<\varepsilon<1/2$, assume there is an $N_0$ such that for all $N\ge N_0$ and all $H$,
--   $$
--   \sum_{m=1}^H\frac{(R_{N,\varepsilon}(m)-P_\varepsilon(m))^2}{m(m+1)}<1,
--   $$
--   where $R_{N,\varepsilon}$ is the finite damped Möbius residual and $P_\varepsilon$ is its explicit pointwise limit. Then every zeta zero with $0<\Re s<1$ has $\Re s=1/2$. Thus even the error tolerance $1$ in the fixed-damping mean-square frontier implies the rational mission’s target. The assumption is the fixed-damping step alone.
-- source:
--   A converse to the fixed-damping convergence frontier https://prove2.me/theorems/b5d23ede-9bcc-4d2a-9c23-84182e886efc. The discrete Hilbert-space Mellin pairing is from B. Bagchi, On Nyman, Beurling and Baez-Duarte’s Hilbert space reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), pp. 137–146, https://arxiv.org/abs/math/0607733. The formalized finite Mellin inequality follows NymanBeurling.finite_remainder_zero_obstruction (Prove2Me submission 657705dd).

import Mathlib
import Definitions.Def_NymanBeurling_DampedResidualLimits

open NymanBeurling
open scoped BigOperators

theorem NymanBeurling.rational_RH_of_fixed_damping_mean_square
    (h : ∀ ε : ℝ, 0 < ε → ε < 1/2 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
        (∑ n ∈ Finset.range H,
          (dampedResidualFinite N ε (n+1) - dampedResidualProfile ε (n+1))^2 /
            ((n+1 : ℝ)*(n+2 : ℝ))) < 1) :
    ∀ (s : ℂ), 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2 := by sorry
