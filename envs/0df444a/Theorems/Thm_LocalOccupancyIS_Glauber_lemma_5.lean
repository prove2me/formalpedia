-- Prove2me | Theorems.Thm_LocalOccupancyIS_Glauber_lemma_5
-- name    : LocalOccupancyIS.Glauber.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:57:28.335653+00:00
-- url     : https://prove2.me/theorems/759c8ba4-09e5-4e32-bb35-340f9eac453e
-- title:
--   Lemma 5 — weighted-degree and average-degree bounds
-- statement:
--   Let $t\ge1$ be an integer, $b\ge0$, and let $F$ be a finite simple graph with $k\ge1$ vertices and $2tN_t(F)\le bk$. Write $s=(b+1)^{1/(2t-1)}$. For real vertex weights $0\le z_v\le p_0$,
--
--   $$\sum_v d_F(v)z_v\le4tsp_0k+4ts^{1/t}k^{1-1/t}\sum_vz_v.$$
--
--   Moreover, the average degree $d$ satisfies
--
--   $$d+1\le4ts\max\{1,(k/s)^{1-1/t}\}.$$
--
--   Both conclusions are included. The common-neighbor density bound controls weighted degree sums used in the occupancy and sweep estimates. Since $k\ge1$, the weight assumptions already imply $p_0\ge0$.
--
--   Differences from the source:
--   - encoding: finite independent sets and induced subgraphs → Boolean configurations on finite types and induced subtypes; reason: these presentations preserve all feasible configurations, including the empty one
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), Lemma 5, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/982.pdf#page=9

import Definitions.Def_LocalOccupancyIS_Glauber_GraphModel

open scoped BigOperators

namespace LocalOccupancyIS.Glauber
/-- Lemma 5, p.9, both (9) and (10). -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (t : ℕ) (ht : 1 ≤ t)
    (b : ℝ) (hb : 0 ≤ b) (hk : 1 ≤ Fintype.card V) (hd : Density F t b)
    (p₀ : ℝ) (z : V → ℝ) (hz : ∀ v, 0 ≤ z v ∧ z v ≤ p₀) :
    let s : ℝ := (b + 1) ^ (1 / (2 * (t : ℝ) - 1))
    (∑ v, (F.degree v : ℝ) * z v) ≤
      4 * t * s * p₀ * Fintype.card V +
        4 * t * s ^ (1 / (t : ℝ)) * (Fintype.card V : ℝ) ^ (1 - 1 / (t : ℝ)) * (∑ v, z v) ∧
    avgDegree F + 1 ≤ 4 * t * s * max 1 (((Fintype.card V : ℝ) / s) ^ (1 - 1 / (t : ℝ))) := by sorry
end LocalOccupancyIS.Glauber
