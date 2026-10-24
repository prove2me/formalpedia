-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_nesterov_theorem
-- name    : ModernConvex.Relaxations.nesterov_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:02.874996+00:00
-- url     : https://prove2.me/theorems/cbafd501-6481-4089-a37c-01a607f0eb25
-- title:
--   Theorem 4.3.2 — Nesterov's theorem: SDP ≥ OPT ≥ (2/π)·SDP for A ⪰ 0
-- statement:
--   Let $A$ be a positive semidefinite $n\times n$ real matrix. Let $\mathrm{OPT}$ be the optimal value of the maximization of the quadratic form $x^TAx$ over $\pm1$ vectors,
--   $$(4.3.17)\qquad \max_x\{x^TAx : x \in S_n\},\qquad S_n = \{x \in \mathbb R^n : x_i \in \{-1, 1\},\ i = 1,\dots,n\},$$
--   and let $\mathrm{SDP}$ be the optimal value of its semidefinite relaxation
--   $$(4.3.18)\qquad \max_X\{\operatorname{Tr}(AX) : X = X^T \succeq 0,\ X_{ii} = 1,\ i = 1,\dots,n\}.$$
--   Then
--   $$\mathrm{SDP} \ge \mathrm{OPT} \ge \frac{2}{\pi}\,\mathrm{SDP} \qquad \Big[\tfrac{2}{\pi} = 0.6366\ldots\Big].$$
--
--   Maximizing a positive semidefinite quadratic form over the vertices of the cube is NP-complete; the theorem says that the semidefinite relaxation, computable in polynomial time, overestimates the optimum by a factor at most $\pi/2$.
--
--   **Formalization Note** $\mathrm{OPT}$ and $\mathrm{SDP}$ enter through the hypotheses "$v$ is the least upper bound of the objective over the feasible set", written out in the statement itself (it imports only Mathlib); both feasible sets are nonempty and the objectives bounded on them, so both values exist for every $A$. The conclusion is the two inequalities $\mathrm{OPT} \le \mathrm{SDP}$ and $\frac{2}{\pi}\mathrm{SDP} \le \mathrm{OPT}$. Positive semidefiniteness is `Matrix.PosSemidef`, which includes symmetry.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 173, Theorem 4.3.2 (Nesterov's theorem) (problems (4.3.17), (4.3.18), p. 173)

import Mathlib

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Theorem 4.3.2 (Nesterov's theorem), p. 173: let `A` be positive
semidefinite, `OPT` the optimal value of `max_x {xᵀAx : x ∈ Sₙ}` (4.3.17), `Sₙ` the vectors with
coordinates `±1`, and `SDP` the optimal value of its semidefinite relaxation
`maximize Tr(AX) s.t. X = Xᵀ ⪰ 0, Xᵢᵢ = 1, i = 1, …, n` (4.3.18). Then `SDP ≥ OPT ≥ (2/π) SDP`.
Each optimal value is given as the least upper bound of the objective over the feasible set. -/
theorem nesterov_theorem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (OPT SDP : ℝ)
    (hOPT : IsLUB ((fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x)) ''
      {x | ∀ i, x i = 1 ∨ x i = -1}) OPT)
    (hSDP : IsLUB ((fun X : Matrix (Fin n) (Fin n) ℝ => (A * X).trace) ''
      {X | X.PosSemidef ∧ ∀ i, X i i = 1}) SDP) :
    OPT ≤ SDP ∧ 2 / Real.pi * SDP ≤ OPT := by sorry

end ModernConvex.Relaxations
