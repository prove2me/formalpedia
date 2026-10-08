-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_zhat_optimal
-- name    : NestedLogitVariants.PartialCompetitive.zhat_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:07:41.563786+00:00
-- url     : https://prove2.me/theorems/64628685-e408-48e2-85c2-8d9c3181537e
-- title:
--   pp. 23–24 — the greedy fill ẑ_i(ϵ_i) is optimal for the continuous knapsack (11) and has at most one fractional component
-- statement:
--   Fix a nest $i$ of a nested logit instance (revenues ordered $r_{i1} \ge \dots \ge r_{in}$, weights $v_{ij} > 0$) and a capacity $\epsilon_i \ge 0$. Let $\hat z_i(\epsilon_i)$ be the greedy solution of the continuous knapsack problem (11): fill the capacity with the eligible products ($v_{ij} \le \epsilon_i$) in revenue order, each fully while it fits and the next one fractionally. Then:
--
--   1. $\hat z_i(\epsilon_i)$ is feasible for (11): $\sum_j v_{ij}\hat z_{ij}(\epsilon_i) \le \epsilon_i$ and $0 \le \hat z_{ij}(\epsilon_i) \le \mathbf 1(v_{ij} \le \epsilon_i)$;
--   2. it is optimal for (11): for every feasible $z_i$,
--   $$\sum_{j \in N} r_{ij} v_{ij} z_{ij} \le \sum_{j \in N} r_{ij} v_{ij} \hat z_{ij}(\epsilon_i) = \hat K_i(\epsilon_i);$$
--   3. at most one component $\hat z_{ij}(\epsilon_i)$ lies strictly between $0$ and $1$.
--
--   Optimality of the greedy fill identifies $\hat K_i(\epsilon_i)$, and the single fractional component is what makes the case analysis of the proof of Theorem 10 possible.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 23–24, the paragraph after display (11)

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- pp. 23–24: the greedy fill `ẑ_i(ε)` is feasible for (11), optimal for (11), and has at most
one fractional component. -/
theorem zhat_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    feas11 I i ε (zhat I i ε) ∧
      (∀ z : Fin n → ℝ, feas11 I i ε z →
        ∑ j, I.r i j * I.v i j * z j ≤ ∑ j, I.r i j * I.v i j * zhat I i ε j) ∧
      (∀ j k : Fin n, zhat I i ε j ∈ Set.Ioo (0 : ℝ) 1 → zhat I i ε k ∈ Set.Ioo (0 : ℝ) 1 →
        j = k) := by sorry

end NestedLogitVariants.PartialCompetitive
