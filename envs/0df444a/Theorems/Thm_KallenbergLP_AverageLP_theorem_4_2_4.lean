-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_2_4
-- name    : KallenbergLP.AverageLP.theorem_4_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:34:23.198977+00:00
-- url     : https://prove2.me/theorems/a78eb75e-00f6-4178-ac88-d9ee462d0fb8
-- title:
--   Theorem 4.2.4 — an extreme optimal solution of the multichain LP yields a pure stationary average optimal policy
-- statement:
--   Consider a finite Markov decision model with state set $E$, finite action sets $A(i)$, rewards $r_{ia}$ and transition probabilities with $\sum_jp_{iaj}=1$, with no assumption on the chain structure. Fix $\beta_j>0$ with $\sum_j\beta_j=1$ and consider the linear program (4.2.11)
--   $$\max\Big\{\sum_i\sum_ar_{ia}x_{ia}\ \Big|\ \sum_i\sum_a(\delta_{ij}-p_{iaj})x_{ia}=0,\ \ \sum_ax_{ja}+\sum_i\sum_a(\delta_{ij}-p_{iaj})y_{ia}=\beta_j\ (j\in E);\ x,y\ge0\Big\}.$$
--   Let $(x^*,y^*)$ be an optimal solution that is an extreme point of the set of feasible solutions, and let $E_{x^*}=\{i\mid\sum_ax^*_{ia}>0\}$. Then a decision rule $f_*$ with
--   $$x^*_{if_*(i)}>0\ \ (i\in E_{x^*}),\qquad y^*_{if_*(i)}>0\ \ (i\in E\setminus E_{x^*})$$
--   exists, and for every such $f_*$ the pure stationary policy $f_*^\infty$ is average optimal: $\phi_i(f_*^\infty)=\sup_R\phi_i(R)$ for every $i\in E$, the supremum running over all policies.
--
--   Since the simplex method returns an extreme optimal solution, this turns one linear program into an average optimal policy for a general multichain model.
--
--   **Formalization Note** Every $f_*$ obeying the rule is covered (Remark 4.2.4: an arbitrary positive variable may be chosen). The average reward is the lim inf criterion.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 103, Theorem 4.2.4; (4.2.10)–(4.2.11), p. 102

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.2.4.** If `(x*, y*)` is an optimal solution of the linear program (4.2.11) such that
`(x*, y*)` is an extreme point of the set of feasible solutions, then the policy `f_*^∞`, where
`f_*(i) := a_i` such that `x*_{i a_i} > 0` for `i ∈ E_{x*}` and `y*_{i a_i} > 0` for
`i ∈ E ∖ E_{x*}`, is an average optimal policy.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 103, Theorem 4.2.4; `β_j > 0`, `Σ_j β_j = 1` from (4.2.10), p. 102.

**Formalization Note.** The conclusion has two parts: such an `f_*` exists (the book's "hence
the policy `f_*^∞` is well-defined", p. 103), and *every* `f_*` obeying the rule gives an average
optimal policy (Remark 4.2.4). Average optimality is `φ(f_*^∞) = φ` against all
history-dependent randomized policies. No unichain or ergodicity assumption is made. -/
theorem theorem_4_2_4 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z) :
    (∃ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf) ∧
    ∀ (f : S → A) (hf : ∀ i, f i ∈ M.admissible i), IsSelection M z.1 z.2 f hf →
      IsAvgOptimal M (stationaryPolicy M f hf) := by sorry

end KallenbergLP.AverageLP
