-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_theorem_10
-- name    : NestedLogitVariants.PartialCompetitive.theorem_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:07:59.262142+00:00
-- url     : https://prove2.me/theorems/824604b0-287f-4de0-889a-48c20d20613f
-- title:
--   Theorem 10, p. 24 — with γ_i ≤ 1, the optimum (x̂, ŷ) of (4) over {Ŝ_i(ϵ_i)} ∪ {{j}} gives (2x̂, 2ŷ) feasible for (3)
-- statement:
--   Consider a nested logit instance in which every dissimilarity parameter satisfies $\gamma_i \le 1$, while the within-nest no-purchase weights $v_{i0} \ge 0$ are arbitrary. For each nest $i$ take as candidate assortments the greedy assortments of the continuous knapsack problem together with the singletons,
--
--   $$\{\hat S_i(\epsilon_i) : \epsilon_i \in [0, \infty]\} \cup \{\{j\} : j \in N\},$$
--
--   and let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) restricted to these candidates. Then $(2\hat x, 2\hat y)$ is feasible for the full linear program (3):
--
--   $$v_0\, 2\hat x \ge \sum_{i \in M} 2\hat y_i, \qquad 2\hat y_i \ge V_i(S_i)^{\gamma_i}\big(R_i(S_i) - 2\hat x\big) \quad \forall S_i \subseteq N,\ i \in M.$$
--
--   Combined with Theorem 1 of the paper, this yields a factor-two approximation for assortment optimization under the nested logit model with partially-captured nests, where the exact problem is NP-hard, using a linear program with polynomially many constraints.
--
--   **Formalization Note** An optimal solution of (4) is a feasible pair whose $x$ is no larger than that of any feasible pair. $2\hat y$ is the componentwise double of $\hat y$. The value $\epsilon_i = \infty$ of the candidate collection is represented by real capacities, since every capacity at least $\sum_j v_{ij}$ already gives $\hat S_i = N$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 24, Theorem 10 (proof in Appendix A.3, pp. 45–46)

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- Theorem 10, p. 24: with dissimilarity parameters at most one, if `(x̂, ŷ)` is an optimal
solution of (4) with the candidate collections `{Ŝ_i(ε) : ε ∈ [0, ∞]} ∪ {{j} : j ∈ N}`, then
`(2 x̂, 2 ŷ)` is feasible for (3). -/
theorem theorem_10 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidates I) xh yh) :
    LP3Feasible I (2 * xh) (2 • yh) := by sorry

end NestedLogitVariants.PartialCompetitive
