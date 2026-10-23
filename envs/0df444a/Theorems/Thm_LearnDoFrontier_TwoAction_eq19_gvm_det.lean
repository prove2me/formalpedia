-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_eq19_gvm_det
-- name    : LearnDoFrontier.TwoAction.eq19_gvm_det
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:38.997277+00:00
-- url     : https://prove2.me/theorems/8e1977f3-240a-4479-8b90-f301a524d9dc
-- title:
--   §4.3, Eq. (19), p. 21 — determinant of the generalized (confluent) Vandermonde matrix
-- statement:
--   Let $z_1, \dots, z_r \in \mathbb C$ be distinct and $m_1, \dots, m_r \ge 1$, $n = \sum_i m_i$. Let $W$ be the generalized Vandermonde matrix (19): the $n \times n$ matrix whose rows are indexed by $k = 0, \dots, n-1$ and whose columns are indexed by the pairs $(i, \tau)$, $0 \le \tau \le m_i - 1$, ordered by $i$ first and $\tau$ second, with entry $\binom{k}{\tau} z_i^{k-\tau}$ (the column block of $z_i$ is $z_i^k$, $\binom{k}{1} z_i^{k-1}$, $\binom{k}{2} z_i^{k-2}$, …). Then
--   $$\det W = \prod_{1 \le i < j \le r} (z_j - z_i)^{m_j m_i} \neq 0.$$
--
--   The nonsingularity of $W$ is what makes the sequences $\binom{k}{\tau} z_i^{k-\tau}$ a basis of the solution space of (16), and it is the model for the matrix $Y$ of Theorem 6.
--
--   **Formalization Note** Columns are relabelled lexicographically into `Fin n`; with that order the sign of the determinant is the one displayed. Natural-number subtraction in the exponent is harmless because $\binom{k}{\tau} = 0$ when $k < \tau$.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), p. 21, §4.3, Eq. (19)

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra

namespace LearnDoFrontier.TwoAction

theorem eq19_gvm_det {r : ℕ} (z : Fin r → ℂ) (m : Fin r → ℕ)
    (hz : Function.Injective z) (hm : ∀ i, 1 ≤ m i) :
    (GVM z m).det = ∏ i : Fin r, ∏ j ∈ Finset.Ioi i, (z j - z i) ^ (m j * m i) ∧
      (GVM z m).det ≠ 0 := by sorry

end LearnDoFrontier.TwoAction
