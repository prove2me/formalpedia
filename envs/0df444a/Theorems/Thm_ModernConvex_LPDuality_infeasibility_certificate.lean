-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_infeasibility_certificate
-- name    : ModernConvex.LPDuality.infeasibility_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:26.813623+00:00
-- url     : https://prove2.me/theorems/0d4c8360-900f-4c23-ab14-f8434fa6374d
-- title:
--   Proposition 1.3.1 — a solution of $\mathcal T_{\rm I}$ or $\mathcal T_{\rm II}$ certifies that $(\mathcal S)$ is infeasible
-- statement:
--   Let $a_1,\dots,a_m \in \mathbb R^n$, $b \in \mathbb R^m$ and $0 \le m_s \le m$, and consider the system $(\mathcal S)$ of linear inequalities in $x \in \mathbb R^n$
--   $$a_i^Tx > b_i\ (i = 1,\dots,m_s), \qquad a_i^Tx \ge b_i\ (i = m_s+1,\dots,m),$$
--   together with the systems in $\lambda \in \mathbb R^m$
--   $$\mathcal T_{\rm I}:\ \lambda \ge 0,\ \sum_{i=1}^m\lambda_ia_i = 0,\ \sum_{i=1}^m\lambda_ib_i \ge 0,\ \sum_{i=1}^{m_s}\lambda_i > 0; \qquad \mathcal T_{\rm II}:\ \lambda \ge 0,\ \sum_{i=1}^m\lambda_ia_i = 0,\ \sum_{i=1}^m\lambda_ib_i > 0.$$
--   If at least one of $\mathcal T_{\rm I}$, $\mathcal T_{\rm II}$ is solvable, then $(\mathcal S)$ is infeasible.
--
--   This is the "easy half" of the general theorem on the alternative: a solution of $\mathcal T_{\rm I}$ or $\mathcal T_{\rm II}$ is a certificate of infeasibility.
--
--   **Formalization Note** The systems are the definitions `SystemS`, `SystemTI`, `SystemTII` (0-based indices: the strict rows are $i < m_s$).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 13–14, Proposition 1.3.1

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_AlternativeSystems

open Matrix

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Proposition 1.3.1, pp. 13–14: if `T_I` or `T_II` is solvable, then
`(S)` is infeasible. -/
theorem infeasibility_certificate {m n : ℕ} (ms : ℕ) (hms : ms ≤ m) (a : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hT : (∃ l : Fin m → ℝ, SystemTI ms a b l) ∨ (∃ l : Fin m → ℝ, SystemTII a b l)) :
    ¬ ∃ x : Fin n → ℝ, SystemS ms a b x := by sorry

end ModernConvex.LPDuality
