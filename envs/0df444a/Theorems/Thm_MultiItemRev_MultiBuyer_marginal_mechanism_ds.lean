-- Prove2me | Theorems.Thm_MultiItemRev_MultiBuyer_marginal_mechanism_ds
-- name    : MultiItemRev.MultiBuyer.marginal_mechanism_ds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:47.267355+00:00
-- url     : https://prove2.me/theorems/fa36a06b-92f9-462d-836d-cbd60e5c33db
-- title:
--   p. 50 — the marginal mechanism q̂ʲ(y) = qʲ₁(y,z), ŝʲ(y) = sʲ(y,z) − qʲ₂(y,z) zʲ is feasible, IC-DS and IR-DS
-- statement:
--   Let $(q, s) = (q^j, s^j)_{j=1,\dots,n}$ be a feasible, IC-DS and IR-DS mechanism for two goods and $n$ buyers, and fix a vector $z \in \mathbb R^n_+$ of the buyers' values for the second good. Define a one-good mechanism $(\hat q, \hat s)$ on $y \in \mathbb R^n_+$ by
--   $$\hat q^j(y) = q^j_1(y, z), \qquad \hat s^j(y) = s^j(y, z) - q^j_2(y, z)\,z^j \qquad (j = 1, \dots, n).$$
--   Then $(\hat q, \hat s)$ is feasible ($\hat q^j \in [0,1]$ and $\sum_j \hat q^j \le 1$), IC-DS and IR-DS.
--
--   This is the reduction of the proof of Theorem 33: the buyers' payoffs in $(\hat q, \hat s)$ at $y$ are their payoffs in $(q,s)$ at $(y,z)$, so the revenue the two-good mechanism collects when the first good's maximal value is the larger one is controlled by a one-good mechanism.
--
--   **Formalization Note** The two-good profile $(y, z)$ is `fun l => ![y l (), z l]`; good 1 is index `0` and good 2 is index `1`. Measurability of $\hat s$ is not part of the statement.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 49–50, proof of Theorems 33 and 34 (definition of (q̂, ŝ) and the sentence 'The mechanism (q̂, ŝ) is IC and IR for y')

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-- p. 50: for a feasible, IC-DS and IR-DS two-good mechanism `(q, s)` and every fixed vector
`z ∈ ℝ^n_+` of the buyers' values for the second good, the one-good mechanism
`q̂^j(y) = q^j_1(y, z)`, `ŝ^j(y) = s^j(y, z) - q^j_2(y, z) z^j` is feasible, IC-DS and IR-DS. -/
theorem marginal_mechanism_ds {n : ℕ} (M : MechanismN n (Fin 2))
    (hF : IsFeasibleN M) (hIC : IsICDS M) (hIR : IsIRDS M) (z : Fin n → ℝ≥0) :
    IsFeasibleN (marginalMech M z) ∧ IsICDS (marginalMech M z) ∧ IsIRDS (marginalMech M z) := by sorry

end MultiItemRev.MultiBuyer
