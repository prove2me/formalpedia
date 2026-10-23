-- Prove2me | Theorems.Thm_GilmoreGomory1961_slack_elimination_p851_faithful
-- name    : GilmoreGomory1961.slack_elimination_p851_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:28:44.847564+00:00
-- url     : https://prove2.me/theorems/ef00a2f2-4159-4907-94a2-88b1d1443831
-- title:
--   p. 851 — every real feasible solution has an equal-cost feasible solution with zero slacks
-- statement:
--   Consider a cutting-stock instance with ordered piece lengths $\ell_1,\dots,\ell_m>0$ and demands $N_1,\dots,N_m\in\mathbb N$, and stock lengths $L_1,\dots,L_k$ with costs $c_1,\dots,c_k$. The columns of the linear program are the cutting patterns $a\in\mathbb Z_{\ge 0}^m$ with $\sum_i\ell_i a_i\le L_j$ (cost $c_j$) and the slack columns $-e_i$ (cost $0$); a feasible solution is a nonnegative real weighting $x$ of finitely many columns whose weighted sum is $N$ (equations (2)–(3)). Then for every feasible $x$
--
--   $$\exists\, x' \text{ feasible}:\quad \operatorname{cost}(x')=\operatorname{cost}(x),\qquad x'_{\text{slack } i}=0 \ \text{ for all } i.$$
--
--   This is the remark on p. 851 of Gilmore and Gomory (1961) that, once integrality is dropped, the slack variables can be removed from (2); it lets the linear program be posed with equality constraints over cutting patterns only.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961) 849–859, doi:10.1287/opre.9.6.849, p. 851

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Model

open GilmoreGomory61.CuttingStock

theorem GilmoreGomory1961.slack_elimination_p851_faithful {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (z : Col I →₀ ℝ) (hz : Feasible I z) :
    ∃ z' : Col I →₀ ℝ, Feasible I z' ∧ cost I z' = cost I z ∧
      ∀ i : Fin m, z' (Sum.inr i) = 0 := by sorry
