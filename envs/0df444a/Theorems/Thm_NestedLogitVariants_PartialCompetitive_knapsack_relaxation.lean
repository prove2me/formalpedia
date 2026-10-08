-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_knapsack_relaxation
-- name    : NestedLogitVariants.PartialCompetitive.knapsack_relaxation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:07:48.33051+00:00
-- url     : https://prove2.me/theorems/7538d2cf-998b-48ea-afab-c07f464ec460
-- title:
--   p. 23 — problem (11) relaxes problem (9), so K̂_i(ϵ_i) ≥ K_i(ϵ_i)
-- statement:
--   Fix a nest $i$ of a nested logit instance (preference weights $v_{ij} > 0$) and a capacity $\epsilon_i \ge 0$. Let $K_i(\epsilon_i)$ be the optimal value of the 0–1 knapsack problem (9) and $\hat K_i(\epsilon_i)$ that of its continuous relaxation (11):
--
--   $$\hat K_i(\epsilon_i) = \max\Big\{\sum_{j \in N} r_{ij} v_{ij} z_{ij} : \sum_{j \in N} v_{ij} z_{ij} \le \epsilon_i,\ 0 \le z_{ij} \le \mathbf 1(v_{ij} \le \epsilon_i)\ \forall j \in N\Big\}.$$
--
--   Then (11) is a relaxation of (9): for every assortment $S \subseteq N$ with $\sum_{j \in S} v_{ij} \le \epsilon_i$, the indicator vector $z_{ij} = \mathbf 1(j \in S)$ is feasible for (11). Consequently $\hat K_i(\epsilon_i) \ge K_i(\epsilon_i)$: some feasible point of (11) has objective value at least $K_i(\epsilon_i)$. This is the inequality used in (28) and (29).
--
--   **Formalization Note.** $\hat K_i$ is not defined as a number; $\hat K_i(\epsilon_i) \ge K_i(\epsilon_i)$ is stated as the existence of a point of (11) whose objective is at least $K_i(\epsilon_i)$, which is the same since the maximum of (11) is attained. The capacity is $\epsilon_i \ge 0$ as on the page ($\epsilon_i \in [0, \infty]$); `Kval` takes a junk value for $\epsilon_i < 0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 23, sentence after display (11)

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- p. 23: problem (11) relaxes problem (9): the indicator vector of every knapsack-feasible
assortment `S` (`∑_{j ∈ S} v_{ij} ≤ ε`) is feasible for (11); hence `K̂_i(ε) ≥ K_i(ε)`, stated as:
some feasible point of (11) has objective value at least `K_i(ε)`. -/
theorem knapsack_relaxation {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (i : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ S : Finset (Fin n), ∑ j ∈ S, I.v i j ≤ ε →
      feas11 I i ε (fun j => if j ∈ S then 1 else 0)) ∧
    ∃ z : Fin n → ℝ, feas11 I i ε z ∧ Kval I i ε ≤ ∑ j, I.r i j * I.v i j * z j := by sorry

end NestedLogitVariants.PartialCompetitive
