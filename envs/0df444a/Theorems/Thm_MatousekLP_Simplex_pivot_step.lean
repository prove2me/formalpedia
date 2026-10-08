-- Prove2me | Theorems.Thm_MatousekLP_Simplex_pivot_step
-- name    : MatousekLP.Simplex.pivot_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:03:23.895993+00:00
-- url     : https://prove2.me/theorems/383d220b-10a1-4775-abb4-82847633ef26
-- title:
--   Lemma 5.6.1 — a pivot step leads to a feasible basis, or detects unboundedness
-- statement:
--   Let $A$ be a real $m\times n$ matrix of rank $m$ with $n\ge m$, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$, and let $B=\{k_1<\dots<k_m\}$ be a feasible basis with complement $N=\{\ell_1<\dots<\ell_{n-m}\}$ and simplex tableau $x_B=p+Qx_N$, $z=z_0+r^Tx_N$. Let $x_v$, $v=\ell_\beta$, be a nonbasic variable with $r_\beta>0$ (an admissible entering variable).
--
--   1. If $x_u$, $u=k_\alpha$, satisfies the leaving criterion
--   $$q_{\alpha\beta}<0\quad\text{and}\quad -\frac{p_\alpha}{q_{\alpha\beta}}=\min\Bigl\{-\frac{p_i}{q_{i\beta}}: q_{i\beta}<0\Bigr\},$$
--   then $B'=(B\setminus\{u\})\cup\{v\}$ is again a feasible basis.
--   2. If no $x_u$ satisfies it, i.e. $q_{i\beta}\ge 0$ for all $i$, then the linear program is unbounded. More precisely, there is a family $x(t)$, $t\in\mathbb{R}$, of solutions of $Ax=b$ with $x_v(t)=t$ and all other nonbasic variables $0$; $x(t)$ is feasible for every $t\ge0$, and $c^Tx(t)\to\infty$ as $t\to\infty$.
--
--   The lemma shows that the simplex method moves from feasible basis to feasible basis, and that it stops only at an optimal tableau or with a certificate of unboundedness.
--
--   **Formalization Note** Indices are 0-based; $p$, $Q$, $r$ are the explicit parameters of Lemma 5.5.1. "No $x_u$ satisfies the criterion" is expressed as $q_{i\beta}\ge0$ for all $i$, which is equivalent because a minimum over a nonempty finite set is attained. The standing assumption of §4.2 is a hypothesis.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 68, Lemma 5.6.1 (criteria on pp. 67–68, rule (5.3))

import Mathlib
import Definitions.Def_MatousekLP_Simplex_Tableau
open Matrix Filter

namespace MatousekLP.Simplex

/-- Lemma 5.6.1 (p. 68). Let `B` be a feasible basis and let the entering variable `x_v`,
`v = ℓ_β`, have a positive coefficient `r_β` in the last row of `T(B)`.
(1) If the leaving variable `x_u`, `u = k_α`, satisfies (5.3), then `B′ = (B \ {u}) ∪ {v}` is
again a feasible basis.
(2) If no `x_u` satisfies the criterion (no row has `q_{iβ} < 0`), then the linear program is
unbounded: substituting `t` for `x_v` and `0` for the other nonbasic variables gives, for
every `t ≥ 0`, a feasible solution, and its objective value tends to `+∞` as `t → ∞`.
Standing assumption of §4.2 (p. 44): `n ≥ m` and `A` has rank `m`. -/
theorem pivot_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (B : Finset (Fin n)) (hB : B.card = m)
    (hfeas : IsFeasibleBasisOf A b B hB) (β : Fin (n - m)) (hr : 0 < tableauR A c B hB β) :
    (∀ α : Fin m, IsEnteringLeaving A b c B hB β α →
        IsFeasibleBasis A b (pivotBasis B hB β α)) ∧
      ((∀ i : Fin m, 0 ≤ tableauQ A B hB i β) →
        IsUnbounded A b c ∧
        ∃ x : ℝ → Fin n → ℝ,
          (∀ t, A *ᵥ x t = b ∧ x t (lIdx B hB β) = t ∧
            ∀ j, j ≠ β → x t (lIdx B hB j) = 0) ∧
          (∀ t, 0 ≤ t → MatousekLP.BFS.IsFeasible A b (x t)) ∧
          Tendsto (fun t => c ⬝ᵥ x t) atTop atTop) := by sorry

end MatousekLP.Simplex
