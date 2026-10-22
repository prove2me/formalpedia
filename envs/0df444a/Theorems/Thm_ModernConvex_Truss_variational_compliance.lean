-- Prove2me | Theorems.Thm_ModernConvex_Truss_variational_compliance
-- name    : ModernConvex.Truss.variational_compliance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:31.921524+00:00
-- url     : https://prove2.me/theorems/e777e2c1-bb1d-45f0-ad47-b721103f5fe2
-- title:
--   Proposition 3.4.4 — variational description of compliance
-- statement:
--   Consider a ground structure $(n, m, B_1, \dots, B_n)$, where $B_i$ is an $m \times k_i$ real matrix, a load $f \in \mathbb R^m$ and a truss $t \in \mathbb R^n_+$. Let $A(t) = \sum_i t_iB_iB_i^T$ be the bar-stiffness matrix and $\mathrm{Compl}_f(t) \in \mathbb R \cup \{+\infty\}$ the compliance: $\tfrac12 f^Tv$ for a solution $v$ of $A(t)v = f$, and $+\infty$ if there is none. Associate with these data the potential energy
--   $$\mathcal C_{t,f}(v) = \tfrac12 v^TA(t)v - f^Tv, \qquad v \in \mathbb R^m. \qquad (3.4.43)$$
--   Then $\mathrm{Compl}_f(t)$ is finite if and only if $\mathcal C_{t,f}$ is bounded below on $\mathbb R^m$, and in this case
--   $$-\mathrm{Compl}_f(t) = \min_v \mathcal C_{t,f}(v), \qquad (3.4.44)$$
--   the minimum being attained.
--
--   This is the variational principle of the truss: the equilibrium displacement minimizes the potential energy.
--
--   **Formalization Note** The compliance is `EReal`-valued; "finite" means equal to a real number $c$. Equation (3.4.44) is stated as: some $v$ has $\mathcal C_{t,f}(v) = -c$ and every $v$ has $\mathcal C_{t,f}(v) \ge -c$. The truss condition $t \ge 0$ is a hypothesis.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 122, Proposition 3.4.4

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, Proposition 3.4.4 (variational description of compliance), p. 122. For a
ground structure `(n, m, B₁, …, Bₙ)`, a load `f ∈ ℝᵐ` and a truss `t ∈ ℝⁿ₊`, let
`C_{t,f}(v) = ½ vᵀA(t)v − fᵀv` (3.4.43). Then `Compl_f(t)` is finite iff `C_{t,f}` is bounded below
on `ℝᵐ`, and in this case `−Compl_f(t) = min_v C_{t,f}(v)` (3.4.44): the minimum is attained and
equals `−Compl_f(t)`. -/
theorem variational_compliance {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (f : Fin m → ℝ) (t : Fin n → ℝ)
    (ht : 0 ≤ t) :
    ((∃ c : ℝ, compliance B f t = (c : EReal)) ↔ BddBelow (Set.range (potentialEnergy B t f))) ∧
    (∀ c : ℝ, compliance B f t = (c : EReal) →
      (∃ v, potentialEnergy B t f v = -c) ∧ ∀ v, -c ≤ potentialEnergy B t f v) := by sorry

end ModernConvex.Truss
