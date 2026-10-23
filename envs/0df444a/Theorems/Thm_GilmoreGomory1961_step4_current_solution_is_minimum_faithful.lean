-- Prove2me | Theorems.Thm_GilmoreGomory1961_step4_current_solution_is_minimum_faithful
-- name    : GilmoreGomory1961.step4_current_solution_is_minimum_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:28:54.717928+00:00
-- url     : https://prove2.me/theorems/f1bbe9b9-6e3d-421f-98b3-121fbd7780a1
-- title:
--   Routine step (4), with the paper's standing assumptions on lengths
-- statement:
--   Consider a cutting-stock instance with ordered piece lengths $\ell_1,\dots,\ell_m>0$ and demands $N_1,\dots,N_m\in\mathbb N$, stock lengths $L_1,\dots,L_k>0$ with costs $c_1,\dots,c_k$, and some stock length $L_j\ge\ell_i$ for all $i$. The columns of the linear program are the cutting patterns $a\in\mathbb Z_{\ge 0}^m$ with $\sum_i \ell_i a_i\le L_j$ (cost $c_j$) and the surplus columns $-e_i$ (cost $0$); a feasible solution is a nonnegative real weighting $x$ of finitely many columns whose weighted sum is $N$. Fix a feasible basis of $m$ columns with bordered matrix $B$ (first row $(1,-c_{\beta_1},\dots,-c_{\beta_m})$), let $\bar N=B^{-1}(0,N_1,\dots,N_m)^{\top}\ge 0$, let $x^B$ be the basic solution read off $\bar N$, and let $b_1,\dots,b_m$ be the last $m$ entries of the first row of $B^{-1}$. If
--
--   $$b_i\ge 0 \text{ for every surplus column } i \text{ not in the basis},\qquad \nexists\, j,\ a\in\mathbb Z_{\ge 0}^m:\ \sum_i\ell_i a_i\le L_j,\ \sum_i b_i a_i>c_j,$$
--
--   then $x^B$ is feasible, $\operatorname{cost}(x^B)=\bar N_1$, and $\bar N_1\le\operatorname{cost}(x)$ for every feasible $x$.
--
--   This is routine step (4) of Gilmore and Gomory (1961), with the paper's standing assumptions on the data (positive lengths, some stock length fitting every piece). The existing theorem GilmoreGomory61.CuttingStock.step4_current_solution_is_minimum proves the same conclusion without these assumptions.
--
--   **Formalization Note** The zero pattern is a column; the slack test is the numeric one of step (3), $b_i\ge0$.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961) 849–859, doi:10.1287/opre.9.6.849, pp. 854–855, routine step (4); standing setup p. 850

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

open GilmoreGomory61.CuttingStock

theorem GilmoreGomory1961.step4_current_solution_is_minimum_faithful {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (hL : ∀ j, 0 < I.L j) (hfit : ∃ j : Fin k, ∀ i, I.ℓ i ≤ I.L j)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (h3 : ∀ i, Sum.inr i ∉ Set.range β → 0 ≤ mult I β i)
    (h4 : ∀ j : Fin k, ¬ ∃ a : Fin m → ℕ,
      patLen I a ≤ I.L j ∧ I.c j < ∑ i, mult I β i * (a i : ℝ)) :
    Feasible I (basicSol I β) ∧
    cost I (basicSol I β) = Nbar I β (Sum.inl ()) ∧
    ∀ z : Col I →₀ ℝ, Feasible I z → Nbar I β (Sum.inl ()) ≤ cost I z := by sorry
