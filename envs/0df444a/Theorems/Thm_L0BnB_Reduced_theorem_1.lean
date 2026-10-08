-- Prove2me | Theorems.Thm_L0BnB_Reduced_theorem_1
-- name    : L0BnB.Reduced.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:33.055188+00:00
-- url     : https://prove2.me/theorems/89cfeed9-8bbe-4622-8e58-13ec4f99f901
-- title:
--   Theorem 1 (Reduced Relaxation) — the interval relaxation of the perspective formulation is equivalent to (5)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$ and $\lambda_0,\lambda_2,M>0$. Consider the interval relaxation of the perspective formulation (3),
--   $$
--   \min_{\beta,z,s}\ \tfrac12\|y-X\beta\|_2^2+\lambda_0\sum_{i\in[p]}z_i+\lambda_2\sum_{i\in[p]}s_i
--   \quad\text{s.t.}\quad \beta_i^2\le s_iz_i,\ \ -Mz_i\le\beta_i\le Mz_i,\ \ z_i\in[0,1],\ \ s_i\ge0,\quad i\in[p],
--   $$
--   and the reduced problem (5),
--   $$
--   \min_{\beta\in\mathbb R^p}\ F(\beta):=\tfrac12\|y-X\beta\|_2^2+\sum_{i\in[p]}\psi(\beta_i;\lambda_0,\lambda_2,M)\quad\text{s.t.}\quad\|\beta\|_\infty\le M,
--   $$
--   where $\psi=\psi_1(\cdot;\lambda_0,\lambda_2)=2\lambda_0\mathcal B(\cdot\,\sqrt{\lambda_2/\lambda_0})$ if $\sqrt{\lambda_0/\lambda_2}\le M$ and $\psi=\psi_2(\cdot;\lambda_0,\lambda_2,M)=(\lambda_0/M+\lambda_2M)|\cdot|$ if $\sqrt{\lambda_0/\lambda_2}>M$, with $\mathcal B$ the reverse Huber penalty (4). Let $V_{\mathrm{PR}(M)}$ be the optimal value of (5). The two problems are equivalent in the following sense:
--
--   1. a vector $\beta$ can be completed to a feasible point $(\beta,z,s)$ of the relaxation if and only if $\|\beta\|_\infty\le M$;
--   2. for every $\beta$ with $\|\beta\|_\infty\le M$, the minimum of the relaxation's objective over all $(z,s)$ with $(\beta,z,s)$ feasible exists and equals $F(\beta)$;
--   3. both problems attain their minimum, and both optimal values equal $V_{\mathrm{PR}(M)}$.
--
--   Theorem 1 eliminates the indicator variables $z$ and the conic auxiliary variables $s$: the relaxation is a box-constrained least squares problem with a separable penalty, which is either the reverse Huber penalty or an $\ell_1$ penalty depending on how $\sqrt{\lambda_0/\lambda_2}$ compares with $M$. This reduced form underlies the paper's first-order solver for node relaxations and its dual bounds.
--
--   **Formalization Note** The paper's "equivalent" is formalized as the three clauses above; "minimum" is `IsLeast` (membership plus lower bound), so attainment is asserted and the real `sInf` defining $V_{\mathrm{PR}(M)}$ is never evaluated on an empty or unbounded set. Norms are explicit coordinate sums and $\|\beta\|_\infty\le M$ is $|\beta_i|\le M$ for all $i$. No normalization of $X$ or $y$ is assumed (the unit-norm assumption of the paper begins in Section 3).
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 6, Theorem 1 (with (3), p. 5, and (4)–(5), p. 6); proof p. 28

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber
import Definitions.Def_L0BnB_Reduced_Setup

namespace L0BnB.Reduced

/-- Theorem 1 (Reduced Relaxation), p. 6: the interval relaxation of the perspective formulation (3)
is equivalent to (5), `min F(β)` subject to `‖β‖_∞ ≤ M`. Precisely:
1. `β` extends to a feasible `(β, z, s)` of the relaxation iff `‖β‖_∞ ≤ M`;
2. for every `β` with `‖β‖_∞ ≤ M`, the minimum of the relaxation's objective over `(z, s)` is `F(β)`;
3. both problems attain their minimum, and the common optimal value is `V_{PR(M)}`. -/
theorem theorem_1 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M) :
    (∀ β : Fin p → ℝ, (∃ z s : Fin p → ℝ, PRFeas M β z s) ↔ β ∈ box p M) ∧
    (∀ β ∈ box p M, IsLeast (PRValuesAt X y lam0 lam2 M β) (F X y lam0 lam2 M β)) ∧
    (IsLeast (PRValues X y lam0 lam2 M) (VPR X y lam0 lam2 M) ∧
      IsLeast (F X y lam0 lam2 M '' box p M) (VPR X y lam0 lam2 M)) := by sorry

end L0BnB.Reduced
