-- Prove2me | Theorems.Thm_HetImpatient_FluidSplit_lemma_1
-- name    : HetImpatient.FluidSplit.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:52.787369+00:00
-- url     : https://prove2.me/theorems/fc2e8543-76fe-43cb-b76a-4bdd49d29795
-- title:
--   Lemma 1, p. 1070 — the within-class program (6) needs at most two subclasses
-- statement:
--   Fix a class $i$ of the fluid model, with arrival rate $\Lambda_i > 0$, service rate $\mu_i > 0$, patience survival function $\bar F_i$ and per-customer cost $\bar c_i(w)$ at offered wait $w \in [0,\infty]$, and a capacity $n_i$. Consider any configuration feasible for the within-class program (6): subclasses $j = 1,\dots,J$ with rates $\lambda_{j} \ge 0$, offered waits $w_j$ and capacities $n_j \ge 0$ such that
--   $$\sum_j \lambda_j = \Lambda_i,\qquad \lambda_j\,\bar F_i(w_j) \le n_j\,\mu_i,\qquad \sum_j n_j \le n_i .$$
--   Then there is a configuration $(\lambda'_j, w'_j, n'_j)_{j=1}^{J'}$, also feasible for (6) at $n_i$, with
--   $$J' \le 2 \qquad\text{and}\qquad \sum_{j=1}^{J'} \lambda'_j\,\bar c_i(w'_j) \;\le\; \sum_{j=1}^{J} \lambda_j\,\bar c_i(w_j).$$
--
--   This is the paper's Lemma 1, "the optimal number of subclasses in (6) satisfies $J^*(i) \le 2$", restated by the authors from Bassamboo and Randhawa (2015): within a single class, splitting into more than two FCFS subclasses never helps. It is the single-class form of Proposition 1.
--
--   **Formalization Note.** "The optimal number of subclasses satisfies $J^*(i)\le 2$" is stated in reduction form: every feasible configuration is weakly improved by a feasible one with at most two subclasses. Whenever (6) has an optimal solution, this yields an optimal solution with at most two subclasses, which is the paper's claim, and it does not depend on the infimum in (6) being attained. It does not say that every optimal solution has at most two subclasses, which fails when costs tie. The standing assumptions of the model ($\Lambda_i>0$, $\mu_i>0$, $\bar F_i$ a survival function with $\bar F_i(\infty)=0$) are hypotheses; costs may have any sign.
-- source:
--   Bassamboo, Randhawa & Wu, Optimally scheduling heterogeneous impatient customers, Manufacturing & Service Operations Management 25(3):1066–1080 (2023), p. 1070, Lemma 1 (restated from Bassamboo & Randhawa 2015)

import Mathlib
import Definitions.Def_HetImpatient_FluidSplit_Model

namespace HetImpatient.FluidSplit

theorem lemma_1 {m : ℕ} (D : ClassData m) (hD : D.Standing) (i : Fin m) (ni : ℝ)
    (c : Config) (hc : ClassFeasible D i ni c) :
    ∃ c' : Config, ClassFeasible D i ni c' ∧ classCost D i c' ≤ classCost D i c ∧
      c'.J ≤ 2 := by sorry

end HetImpatient.FluidSplit
