-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_9
-- name    : OnlineMatchFrameworks.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:29:52.673061+00:00
-- url     : https://prove2.me/theorems/5352f9db-4a3d-46ba-9eb1-adffbd36ce38
-- title:
--   Theorem 9: SimpleGreedy is at most $1/2$-competitive, even for uniform $p=O(1/n)$
-- statement:
--   In the unweighted stochastic rewards problem every weight and every patience equals $1$. SimpleGreedy probes, for each arriving vertex, an arbitrary edge to an unmatched neighbor. For every $\varepsilon>0$ there is a constant $C>0$ such that for every $N$ there are an instance with $|U|\ge N$ whose edges all have one probability $p\le C/|U|$, an arrival order and a choice rule of SimpleGreedy with $\mathrm{OPT}(G)>0$ and
--
--   $$
--   \mathrm{ALG}(G)\ \le\ \Bigl(\frac12+\varepsilon\Bigr)\mathrm{OPT}(G).
--   $$
--
--   Since every opportunistic algorithm is $1/2$-competitive, the factor $1/2$ is tight for SimpleGreedy even with small uniform probabilities.
--
--   Differences from the source:
--   - reading: a family with competitive ratio at most 1/2 → for every ε > 0 instances with ALG ≤ (1/2 + ε)·OPT; reason: the ratio of the construction is 1/2 + o(1) as k → ∞ (p.54), so 1/2 is an infimum
--   - reading: p = O(1/n) → a constant C, which may depend on ε, with p ≤ C/|U| on arbitrarily large |U|; reason: n is the size parameter of U in the construction (|U| = k + n, p = k/n for fixed k, p.31)
--   - reading: chooses a neighbor arbitrarily (p.31) → some rule that picks an unmatched neighbor from the unmatched set and the arriving vertex; reason: an arbitrary choice may be the worst one (p.54); exhibiting a rule without memory is enough
--   - reading: the adversary sets the arrival order (p.11); the offline algorithm probes U_0 × V_0 first (p.31) → some duplicate-free order of all of V, and the published OPT, which picks its own order; reason: the model of pp.11–12, as used in the construction
--   - encoding: competitive ratio ALG/OPT → OPT > 0 and ALG ≤ (1/2 + ε)·OPT; reason: the ratio is defined on these instances
--   - encoding: unweighted, θ_v = 1, uniform probability on all edges → w ≡ 1, unit deterministic tail, every p_{u,v} is 0 or p; reason: non-edges have probability 0 (p.11)
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 9, p.31

import Definitions.Def_OnlineMatchFrameworks_Supplement_SimpleGreedy
import Definitions.Def_OnlineMatchFrameworks_Offline
import Definitions.Def_OnlineMatchFrameworks_PatienceModels

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 9.** arXiv:1907.03963v6, Theorem 9, p.31: "There exists a family of unweighted graphs under
stochastic rewards and adversarial arrivals for which SimpleGreedy achieves a competitive ratio of at
most 1/2 even when all edges have uniform probability p = O(1/n)."

**Formalization Note.** For every `ε > 0` there is a constant `C` such that arbitrarily large
instances (`a = |U| ≥ N`) exist with unit weights, unit patience, one probability `p ≤ C/|U|` on every
edge (non-edges have probability `0`), an arrival order and a SimpleGreedy choice rule with
`ALG ≤ (1/2 + ε) OPT`. The `n` of "O(1/n)" is read as the number of offline vertices (`|U| = k + n` in
the construction on p.31). -/
theorem theorem_9 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∃ (a b : ℕ) (G : OnlineMatchFrameworks.Instance (Fin a) (Fin b)) (p : ℝ)
        (choose : Finset (Fin a) → Fin b → Option (Fin a)) (order : List (Fin b)),
        N ≤ a ∧ 0 < a ∧ 0 < p ∧ p ≤ C / (a : ℝ) ∧
        (∀ u v, G.p u v = 0 ∨ G.p u v = p) ∧
        (∀ u, G.w u = 1) ∧
        (∀ v l, G.surv v l =
          OnlineMatchFrameworks.tailSurvival (OnlineMatchFrameworks.deterministicTail fun _ => 1) v l) ∧
        IsSimpleGreedyRule G choose ∧
        order.Nodup ∧ (∀ v, v ∈ order) ∧
        0 < G.OPT ∧
        G.ALG (greedyBox choose) order ≤ (1 / 2 + ε) * G.OPT := by sorry

end OnlineMatchFrameworks.Supplement
