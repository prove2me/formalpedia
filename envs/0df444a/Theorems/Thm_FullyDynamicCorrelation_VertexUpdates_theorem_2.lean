-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_theorem_2
-- name    : FullyDynamicCorrelation.VertexUpdates.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:51:06.502184+00:00
-- url     : https://prove2.me/theorems/83d5a3bc-2ec4-40a2-bc6e-ab9022b3b398
-- title:
--   Theorem 2 — a partially correct tolerant decomposition gives an O(1)-approximation
-- statement:
--   Fix positive constants $C_t,C_l,\eta_d,\eta_l,C_0$ and $\varepsilon_s,\varepsilon_\tau\in(0,1/500]$, $\varepsilon_l\in[0,1/500]$. There is $A>0$ such that for every signed complete graph $G$, every $n\ge|V|$ and every partially correct tolerant $(\varepsilon_s,\varepsilon_\tau,\varepsilon_l)$-sparse-dense decomposition $\{S,T,I\}$ of $G^+$ (Definition 6; $\varepsilon_l=0$ only when there is no isolated cluster), the clustering that keeps each cluster of $T\cup I$ together and every vertex of $S$ alone has cost at most $A\cdot\mathrm{opt}$.
--
--   Differences from the source:
--   - generalization: “for suitable choices of positive constant εs, ετ, εl ≤ 1/500” and O(1) → for every εs, ετ ∈ (0, 1/500] and εl ∈ [0, 1/500] (and every fixed Ct, Cl, ηd, ηl, C0 > 0) there is A > 0, uniform over graphs and n; reason: the bounds of Lemmas 4.6, 4.12 and 4.13 (pp. 25–30) are uniform over graphs for fixed positive parameters, and the only internal-density restriction used is ετ ≤ 1/50; the smaller domain ετ ≤ 1/500 satisfies it. Larger agreement or sparsity products may be truncated to a fixed parameter below 1 for the charging bound, or yield no relevant edges. Every suitable source choice is included
--   - generalization: n, the maximum number of vertices → any n ≥ |V|; reason: n enters only through the level range and log n of Definition 6; the source’s n is one such value
--   - reading: log n in Definition 6 → log₂ n; reason: the degree levels are powers of 2 and L = 1 + ⌈log₂ n⌉
--   - encoding: the partition {Ṽ_singleton, ∪K^tolerant, ∪K^isolate} of V → S, T, I with IsPartition (nonempty, pairwise disjoint, covering clusters); reason: a partition of V
--   - encoding: correlation clustering cost and the optimum → cost and opt of the Graph module (unordered pairs of distinct active vertices; opt the attained minimum over partitions); reason: Problem 1
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Theorem 2, p. 21

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Tolerant

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Theorem 2 (p. 21). -/
theorem theorem_2 (Ct Cl ηd ηl C0 : ℝ) (hCt : 0 < Ct) (hCl : 0 < Cl) (hηd : 0 < ηd)
    (hηl : 0 < ηl) (hC0 : 0 < C0) (εs ετ εl : ℝ) (hεs : 0 < εs) (hεs' : εs ≤ 1 / 500)
    (hετ : 0 < ετ) (hετ' : ετ ≤ 1 / 500) (hεl : 0 ≤ εl) (hεl' : εl ≤ 1 / 500) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (H : SGraph) (n : ℕ), H.V.card ≤ n →
        ∀ (S : Finset ℕ) (T I : Finset (Finset ℕ)), (0 < εl ∨ I = ∅) →
          H.IsPCTD n εs ετ εl Ct Cl ηd ηl C0 S T I →
            (H.cost (decompRel T I) : ℝ) ≤ A * (H.opt : ℝ) := by sorry

end FullyDynamicCorrelation.VertexUpdates
