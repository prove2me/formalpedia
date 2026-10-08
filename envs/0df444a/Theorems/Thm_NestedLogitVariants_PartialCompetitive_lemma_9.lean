-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_lemma_9
-- name    : NestedLogitVariants.PartialCompetitive.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:07:23.259888+00:00
-- url     : https://prove2.me/theorems/d41786f8-a3df-46dd-ac23-711a711edb82
-- title:
--   Lemma 9, p. 23 — with γ_i ≤ 1, problems (3) and (10) have the same optimal solutions
-- statement:
--   Consider a nested logit instance in which every dissimilarity parameter satisfies $\gamma_i \le 1$ (the no-purchase weights $v_{i0} \ge 0$ are arbitrary), with at least one product per nest. Let (3) be the linear program
--
--   $$\min\ x \quad \text{s.t.}\quad v_0 x \ge \sum_{i \in M} y_i,\quad y_i \ge V_i(S_i)^{\gamma_i}(R_i(S_i) - x)\ \ \forall S_i \subseteq N,\ i \in M,$$
--
--   and (10) the program in which the second family of constraints is replaced by $y_i \ge \max_{\epsilon_i \ge 0}\{(v_{i0}+\epsilon_i)^{\gamma_i}[K_i(\epsilon_i)/(v_{i0}+\epsilon_i) - x]\}$. Then for every $x$ and $y = (y_1, \dots, y_m)$,
--
--   $$(x, y) \text{ is optimal for (3)} \iff (x, y) \text{ is optimal for (10)}.$$
--
--   Lemma 9 is what lets §5 work with knapsack problems in place of the assortment problem.
--
--   **Formalization Note** An optimal solution is a feasible pair whose $x$ is no larger than that of any feasible pair. The hypothesis $n \ge 1$ (the paper's $N = \{1, \dots, n\}$ is nonempty) is added: with no products, all $v_{i0} = 0$ and $v_0 = 0$, problem (3) has no optimal solution while $(0, 0)$ is optimal for (10).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 23, Lemma 9

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- Lemma 9, p. 23: with dissimilarity parameters at most one, problems (3) and (10) have the same
optimal solutions. -/
theorem lemma_9 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hn : 0 < n) (x : ℝ) (y : ι → ℝ) :
    LP3Optimal I x y ↔ LP10Optimal I x y := by sorry

end NestedLogitVariants.PartialCompetitive
