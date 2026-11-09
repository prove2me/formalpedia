-- Prove2me | Theorems.Thm_LinearChoresCLS_theorem_6_10
-- name    : LinearChoresCLS.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:59:24.853098+00:00
-- url     : https://prove2.me/theorems/fbb9fdaa-28be-4b76-ac11-bc4b11897819
-- title:
--   Theorem 6.10 — linear approximation, remainder bound $t^3/(2(n+1))$
-- statement:
--   Let $0<t\le1$, $\alpha=\lambda t^2$ as in (5.5), $c_0=-\sum_{i=1}^nc_i$ and $p_j(x)=(1+tx_j)/(1+t\bar x)$ with $x_0=0$. For every $x\in[0,1]^n$,
--   $$
--   \frac\alpha t\sum_{j=0}^nc_j\log p_j(x)=\alpha c^\top x+R_{\mathrm{lin}}(x),\qquad R_{\mathrm{lin}}(x)=\sum_{j=1}^n\frac\alpha tc_j\big(\log(1+tx_j)-tx_j\big).
--   $$
--   For every $\ell\in[n]$ and every coordinate segment from $x$ to $x+he_\ell$ in $[0,1]^n$, $|R_{\mathrm{lin}}(x+he_\ell)-R_{\mathrm{lin}}(x)|\le\frac{t^3}{2(n+1)}|h|$; moreover, for every feasible coordinate direction $\tilde v\in\{\pm e_\ell\}$ at $x$, the right directional derivative exists and $|R'_{\mathrm{lin}}(x;\tilde v)|\le\frac{t^3}{2(n+1)}$.
--
--   The adjustment of the basic earning requirements by $-\frac\alpha tc_j$ produces the linear part $\alpha c^\top x$ of $\alpha Q(x)$.
--
--   Differences from the source:
--   - generalization: t of the construction (rational; (7.1) gives t = 2^{−L} ≤ 1/256) → any real t ∈ (0, 1] (Section 5's range); reason: the statement involves only the basic price family and α = λt²; the proof (p.48) is written for 0 < t < 1/8, but its computation |∂ℓR_lin| = αt|cℓ|xℓ/(1 + t xℓ) ≤ t³/(2(n+1)) uses only t > 0, and (7.1)'s t is an instance
--   - generalization: QP dimension n ≥ 1 (A ∈ ℚ^{n×n}, [n] for positive n, p.5) → any n : ℕ; reason: at n = 0 the box is one point and every clause holds trivially; n ≥ 1 is a special case
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 6.10, Eqs. (6.16)–(6.17), p.27 (proof Appendix C.2, p.48)

import Mathlib
import Definitions.Def_LinearChoresCLS_Remainders
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Theorem 6.10 (Linear approximation)** (arXiv:2611.06589, held version sha256 85d34a9e…,
p.27). Let `α` be given by (5.5) and `c₀ := −∑_{i=1}^n c_i` (6.13). For every `x ∈ [0,1]ⁿ`,
`(α/t) ∑_{j=0}^n c_j log p_j(x) = αcᵀx + R_lin(x)` (6.16); for every `ℓ ∈ [n]` and every coordinate
segment from `x` to `x + he_ℓ` in `[0,1]ⁿ`, `|R_lin(x + he_ℓ) − R_lin(x)| ≤ t³/(2(n+1)) |h|` (6.17);
and for every feasible coordinate direction `ṽ ∈ {±e_ℓ}` at `x` the right directional derivative
exists and `|R′_lin(x; ṽ)| ≤ t³/(2(n+1))`.

**Formalization Note.** `p_j(x)` is the basic price family (5.2) with `x₀ = 0`. The parameter `t`
is any real in Section 5's range `(0, 1]` (p.13); the completed market's `t` of (7.1) is one
instance. -/
theorem theorem_6_10 {n : ℕ} (P : Quadratic n) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (∀ x : Fin n → ℝ, InCube x →
      alpha P t / t * ∑ j, cExt P j * Real.log (basicPrice t x j) =
        alpha P t * ∑ i, (P.c i : ℝ) * x i + Rlin P t x) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single ℓ (1 : ℝ)) →
      |Rlin P t (x + h • Pi.single ℓ (1 : ℝ)) - Rlin P t x| ≤ t ^ 3 / (2 * (n + 1)) * |h|) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (s : Bool), InCube x → FeasibleCoordDir x ℓ s →
      ∃ D : ℝ, HasRightDerivAt0 (fun h => Rlin P t (x + h • coordDir ℓ s)) D ∧
        |D| ≤ t ^ 3 / (2 * (n + 1))) := by sorry

end LinearChoresCLS
