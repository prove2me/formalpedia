-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_theorem_on_alternative
-- name    : ModernConvex.LPDuality.theorem_on_alternative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:27.123185+00:00
-- url     : https://prove2.me/theorems/d1d1a679-15a4-4585-8072-cec8a2856aa4
-- title:
--   Theorem 1.3.1 — general theorem on the alternative: $(\mathcal S)$ is infeasible iff $\mathcal T_{\rm I}$ or $\mathcal T_{\rm II}$ is solvable
-- statement:
--   Let $a_1,\dots,a_m \in \mathbb R^n$, $b \in \mathbb R^m$ and $0 \le m_s \le m$. The system
--   $$(\mathcal S):\quad a_i^Tx > b_i\ (i = 1,\dots,m_s), \qquad a_i^Tx \ge b_i\ (i = m_s+1,\dots,m)$$
--   has no solution $x \in \mathbb R^n$ if and only if either
--   $$\mathcal T_{\rm I}:\ \lambda \ge 0,\ \sum_{i=1}^m\lambda_ia_i = 0,\ \sum_{i=1}^m\lambda_ib_i \ge 0,\ \sum_{i=1}^{m_s}\lambda_i > 0$$
--   or
--   $$\mathcal T_{\rm II}:\ \lambda \ge 0,\ \sum_{i=1}^m\lambda_ia_i = 0,\ \sum_{i=1}^m\lambda_ib_i > 0$$
--   (or both) has a solution $\lambda \in \mathbb R^m$.
--
--   It is the source of the book's LP duality theory: applied to the system $-c^Tx > -a,\ Ax \ge b$ it characterizes the lower bounds on the optimal value of an LP (Proposition 1.3.2).
--
--   **Formalization Note** Same encoding of $(\mathcal S)$, $\mathcal T_{\rm I}$, $\mathcal T_{\rm II}$ as in Proposition 1.3.1 (0-based indices; strict rows $i < m_s$). Both directions are stated.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 14, Theorem 1.3.1 (general theorem on the alternative)

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_AlternativeSystems

open Matrix

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Theorem 1.3.1 (general theorem on the alternative), p. 14: `(S)` has no
solution iff `T_I` or `T_II` (or both) is solvable. -/
theorem theorem_on_alternative {m n : ℕ} (ms : ℕ) (hms : ms ≤ m) (a : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) :
    (¬ ∃ x : Fin n → ℝ, SystemS ms a b x) ↔
      (∃ l : Fin m → ℝ, SystemTI ms a b l) ∨ (∃ l : Fin m → ℝ, SystemTII a b l) := by sorry

end ModernConvex.LPDuality
