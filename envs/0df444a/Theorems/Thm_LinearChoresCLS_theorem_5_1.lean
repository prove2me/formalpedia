-- Prove2me | Theorems.Thm_LinearChoresCLS_theorem_5_1
-- name    : LinearChoresCLS.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:50:40.528408+00:00
-- url     : https://prove2.me/theorems/92a8cebb-1302-4a18-b9a1-404e56f9e2ba
-- title:
--   Theorem 5.1 — quadratic approximation of the basic market, remainder bound $2t^3$
-- statement:
--   Let $0<t\le1$ and consider the basic market of Section 5 with price family $p_j(x)=(1+tx_j)/(1+t\bar x)$, $x_0=0$, and $\Phi_0(x)=\Psi_0(p(x))$. For every $x\in[0,1]^n$,
--   $$
--   \Phi_0(x)=\frac{t^2}{2(n+1)}\sum_{0\le j<j'\le n}(x_j-x_{j'})^2+R_0(x).
--   $$
--   The remainder satisfies $|R_0(x+he_j)-R_0(x)|\le2t^3|h|$ for every $j\in[n]$ and every coordinate segment from $x$ to $x+he_j$ in $[0,1]^n$; moreover, for every feasible coordinate direction $\tilde v\in\{\pm e_j\}$ at $x$, the right directional derivative $R_0'(x;\tilde v)$ exists and $|R_0'(x;\tilde v)|\le2t^3$.
--
--   The basic market contributes a quadratic term proportional to the sum of squared coordinate differences, with third-order error.
--
--   **Formalization Note** $\Phi_0$ is the generic objective of the basic market evaluated at $p(x)$, and $R_0$ is defined by the identity (5.3), as in Appendix B; the content is in the two bounds.
--
--   Differences from the source:
--   - generalization: positive rational t ∈ (0, 1] → real t ∈ (0, 1]; reason: rational t is a special case; the proof uses only 0 < t ≤ 1
--   - generalization: QP dimension n ≥ 1 (A ∈ ℚ^{n×n}, [n] for positive n, p.5) → any n : ℕ; reason: at n = 0 the box is one point and every clause holds trivially; n ≥ 1 is a special case
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 5.1, Eq. (5.3), p.15 (proof Appendix B, pp.45–46)

import Mathlib
import Definitions.Def_LinearChoresCLS_BasicMarket
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Theorem 5.1 (Quadratic approximation)** (arXiv:2611.06589, held version sha256 85d34a9e…,
p.15). For the basic market with parameter `0 < t ≤ 1` and every `x ∈ [0,1]ⁿ`,
`Φ₀(x) = (t²/(2(n+1))) ∑_{0≤j<j′≤n} (x_j − x_{j′})² + R₀(x)` (5.3). The remainder satisfies
`|R₀(x + he_j) − R₀(x)| ≤ 2t³|h|` for every `j ∈ [n]` and every coordinate segment from `x` to
`x + he_j` in `[0,1]ⁿ`; and for every feasible coordinate direction `ṽ ∈ {±e_j}` at `x` the right
directional derivative `R₀′(x; ṽ)` exists and `|R₀′(x; ṽ)| ≤ 2t³`.

**Formalization Note.** `Φ₀` is the generic logarithmic objective of `basicMarket n t` at the
price family (5.2); `x₀ = 0`. The range `t ∈ (0, 1]` is Section 5's (p.13; real instead of
rational `t`). -/
theorem theorem_5_1 {n : ℕ} (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∀ x : Fin n → ℝ, InCube x →
      Phi0 t x = t ^ 2 / (2 * (n + 1)) * ∑ π : Pair n, (xExt x π.1.1 - xExt x π.1.2) ^ 2 +
        R0 t x) ∧
    (∀ (x : Fin n → ℝ) (j : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single j (1 : ℝ)) →
      |R0 t (x + h • Pi.single j (1 : ℝ)) - R0 t x| ≤ 2 * t ^ 3 * |h|) ∧
    (∀ (x : Fin n → ℝ) (j : Fin n) (s : Bool), InCube x → FeasibleCoordDir x j s →
      ∃ D : ℝ, HasRightDerivAt0 (fun h => R0 t (x + h • coordDir j s)) D ∧
        |D| ≤ 2 * t ^ 3) := by sorry

end LinearChoresCLS
