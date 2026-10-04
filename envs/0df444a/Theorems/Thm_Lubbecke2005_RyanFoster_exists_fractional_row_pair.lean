-- Prove2me | Theorems.Thm_Lubbecke2005_RyanFoster_exists_fractional_row_pair
-- name    : Lubbecke2005.RyanFoster.exists_fractional_row_pair
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:41:12.985151+00:00
-- url     : https://prove2.me/theorems/906b47dc-8f6f-42f7-8f3b-95b4d748b51c
-- title:
--   Proposition 3 — a fractional basic solution of $A\lambda = \mathbf 1$, $\lambda \ge \mathbf 0$ covers some pair of rows fractionally
-- statement:
--   This is the Ryan–Foster lemma behind branch-and-price for set-partitioning problems.
--
--   Let $A = (a_{rj}) \in \{0,1\}^{m \times |J'|}$ be a $0/1$ matrix with rows $\{1, \dots, m\}$ and columns indexed by a finite set $J'$. Let $\lambda \in \mathbb R^{J'}$ be a **basic feasible solution** of the system
--
--   $$A\lambda = \mathbf 1, \qquad \lambda \ge \mathbf 0,$$
--
--   in the sense of Bertsimas and Tsitsiklis (Definition 2.9): $\lambda$ satisfies all constraints, and among the constraints active at $\lambda$ (all $m$ equality rows, and those $\lambda_j \ge 0$ with $\lambda_j = 0$) there are $|J'|$ linearly independent ones. Suppose $\lambda$ is **fractional**, $\lambda \notin \{0,1\}^{|J'|}$. Then there exist rows $r, s \in \{1, \dots, m\}$ such that
--
--   $$0 < \sum_{j \in J'} a_{rj}\, a_{sj}\, \lambda_j < 1 .$$
--
--   For $r = s$ the sum is the row sum $\sum_j a_{rj}\lambda_j = 1$, so the two rows found are necessarily distinct. The pair $(r, s)$ is what Ryan–Foster branching branches on: one branch requires the rows to be covered by the same column (the sum equals $1$), the other by two distinct columns (the sum equals $0$), and the current fractional solution satisfies neither. The paper states the proposition and attributes it to Ryan and Foster (1981) without proof.
--
--   **Formalization Note** The paper writes "i.e., $\lambda \notin \{0,1\}^m$"; since $\lambda$ has one coordinate per column, this statement reads it as $\lambda \notin \{0,1\}^{|J'|}$ (a typo correction). "Basic solution" is not defined in the paper; it is read as the textbook notion for the standard-form system, via the platform definitions `LinearOptimization.stdFormSystem` and `LinearOptimization.IsBasicFeasibleSolution`, which need no full-row-rank assumption on $A$. The solution is any fractional basic solution, not necessarily an optimal one. Rows are `Fin m`, columns `Fin n`, $A$ is a real matrix with the $0/1$ property as a hypothesis, and the quantity is `pairCover A lam r s`. For $m = 0$ or $n = 0$ no fractional basic solution exists, so the statement is vacuous there, as on the page.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, p. 1020, Proposition 3

import Mathlib
import Definitions.Def_ActiveConstraints
import Definitions.Def_BasicSolution
import Definitions.Def_Lubbecke2005_RyanFoster_SetPartitioning

open Matrix

namespace Lubbecke2005.RyanFoster

/-- **Proposition 3** (Lübbecke–Desrosiers 2005, §7.3, p. 1020; Ryan and Foster 1981).
Let `A` be an `m × n` matrix with entries in `{0, 1}` (the columns are indexed by
`J′ = Fin n`) and let `λ` be a basic feasible solution of the standard-form system
`Aλ = 𝟏, λ ⩾ 𝟎` (Bertsimas–Tsitsiklis Definition 2.9) which is fractional, i.e.
`λ ∉ {0, 1}^{|J′|}` (the paper's `{0, 1}^m` is a typo: `λ` has one coordinate per
column). Then some rows `r, s` satisfy `0 < ∑_j a_rj a_sj λ_j < 1`. -/
theorem exists_fractional_row_pair {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : IsZeroOneMatrix A) (lam : Fin n → ℝ)
    (hbasic : LinearOptimization.IsBasicFeasibleSolution
      (LinearOptimization.stdFormSystem A (fun _ => 1)) lam)
    (hfrac : ¬ IsZeroOneVector lam) :
    ∃ r s : Fin m, 0 < pairCover A lam r s ∧ pairCover A lam r s < 1 := by sorry

end Lubbecke2005.RyanFoster
