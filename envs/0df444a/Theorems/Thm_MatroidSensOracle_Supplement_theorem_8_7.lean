-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_8_7
-- name    : MatroidSensOracle.Supplement.theorem_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:18:37.074884+00:00
-- url     : https://prove2.me/theorems/91281e38-d681-4432-9272-d10909aa96d8
-- title:
--   Theorem 8.7 ($\alpha$-factors of $G+U$ correspond to $\beta$-factors of $H+U_H$, with cost identity (8))
-- statement:
--   Let $G=(V,E,c)$ be an undirected graph, $\alpha:V\to\mathbb Z_{>0}$, and $M$ a min-cost $\alpha$-factor of $G$. Fix $f\ge1$ and an update set $U$ with $|U|=f$ (deletions of edges of $E$ and insertions of new edges). Put $f_v=\min(2f,\alpha(v))$ and let $H+U_H$ be the auxiliary multigraph of §8.2.2 on the vertices $v_1,v_2,r_v,s_v$ ($v\in V$), with degree bounds $\beta=f_v$ at each copy of $v$: a Layer 1 copy $(a_1,b_1)$ of cost $-c(e)$ of each surviving edge $e\in M$, a Layer 2 copy $(a_2,b_2)$ of cost $c(e)$ of every other edge of $G+U$, $f_v-\mathrm{del}(v)$ zero-cost edges $v_1v_2$ and $s_vr_v$, and for each deleted $(a,b)\in M$ the zero-cost edges $r_ar_b$, $s_aa_1$, $s_bb_1$; here $\mathrm{del}(v)$ is the number of deleted $M$-edges at $v$. The projection of a set $F$ of edges of $H+U_H$ is $M'=(M\setminus D)\cup A$, with $A$ the non-$M$ edges whose Layer 2 copy is in $F$ and $D$ the $M$-edges selected in Layer 1 or deleted by $U$. Then:
--
--   1. $G+U$ has an $\alpha$-factor if and only if $H+U_H$ has a $\beta$-factor;
--   2. for every $\beta$-factor $F$ of $H+U_H$, the projection $M'$ is an $\alpha$-factor of $G+U$ and
--   $$c(M')=c(M)+c_H(F)-\sum_{e\in U\cap M,\ \text{deleted}}c(e);\qquad(8)$$
--   3. the minimum cost of an $\alpha$-factor of $G+U$ equals $c(M)-\sum_{e\in U\cap M\text{ deleted}}c(e)$ plus the minimum cost of a $\beta$-factor of $H+U_H$ (both are $+\infty$ when no factor exists).
--
--   The reduction replaces degree bounds $\alpha$ by bounds $\beta\le2f$, so that the oracle of Theorem 8.3 applies with $k=O(f)$ (Theorem 8.8).
--
--   **Formalization Note** The first edges of $H+U_H$ are the layer copies of the edges of $G+U$ in order, so the projection is read off edge indices.
--
--   Differences from the source:
--   - reading: an update set U ⊆ E with |U| = f; '(a, b) ∉ M (added/removed)' → U = (I, F) with F ⊆ E and insertions of new edges joining distinct vertices, |I| + |F| = f; reason: the translation of U_H on p.43 treats added non-M edges
--   - encoding: H, β, U_H as separate objects → the multigraph H + U_H built in one step (auxGraph), parallel edges interchangeable; reason: the removal of 'one edge each' of a parallel class does not depend on which copy is removed
--   - reading: a min-cost α-factor of G + U corresponds exactly to a min-cost β-factor of H + U_H → min α-factor cost of G + U = c(M) − Σ_{deleted e ∈ M} c(e) + min β-factor cost of H + U_H, in ℤ ∪ {+∞}; reason: the correspondence is the cost identity (8) applied to minimizers
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 8.7, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_AlphaAux

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 8.7 (the `α`-factor ⟺ `β`-factor reduction).** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.43 (PDF p.46): "G + U contains an α-factor if and
only if H + U_H contains a β-factor. Moreover, under the costs assigned above,
c(M′) = c(M) + c_H(F) − Σ_{e∈U∩M, deleted} c(e). (8)
Consequently, a min-cost α-factor of G + U corresponds exactly to a min-cost β-factor of H + U_H, and
(ignoring costs) existence transfers bi-directionally." Setting (§8.2.2, pp.41–43): `M` is a
precomputed min-cost `α`-factor of `G`, `f_v = min(2f, α(v))`, the auxiliary graph `H` with degree
bounds `β`, the translation `U_H` of an update set `U` with `|U| = f`, and the projection
`M′ = (M ∖ D) ∪ A` of a `β`-factor `F` of `H + U_H`.

**Formalization Note.**
* `G` is an undirected input graph (edges `(a, b)`, `a < b`), `α : V → ℤ_{>0}`, `M ⊆ E` a min-cost
  `α`-factor of `G` (`IsMinCostFactorSet`), `f ≥ 1`, and `U = (I, F)` an update with `F ⊆ E`, inserted
  edges joining distinct vertices, and `|U| = f`. Inserted edges are new edges (never in `M`);
  "for (a, b) ∉ M (added/removed): apply the identical operation to (a₂, b₂)" is read as allowing
  insertions as well as deletions.
* `H + U_H` is `auxGraph G α M f U`, `β` is `auxBeta α f`, the projection is `proj`, all as built on
  pp.42–43 (see the definitions). Factors are sets of edges of these multigraphs.
* The three clauses: (i) existence transfers both ways; (ii) for every `β`-factor `F` of `H + U_H`, its
  projection `M′` is an `α`-factor of `G + U` and satisfies (8); (iii) the least cost of an
  `α`-factor of `G + U` equals `c(M) − Σ_{e ∈ F ∩ M} c(e)` plus the least cost of a `β`-factor of
  `H + U_H` (both `⊤` when none exists). -/
theorem theorem_8_7 :
    ∀ (n : ℕ) (G : InputGraph n) (α : Fin n → ℕ) (M : Finset (Fin n × Fin n)) (f : ℕ) (U : Update n),
      G.Undirected → (∀ v, 1 ≤ α v) → IsMinCostFactorSet G α M → 1 ≤ f →
      G.ValidUPlain f U → U.size = f →
        let delCost : ℤ := ∑ e ∈ U.del ∩ M, G.cost e
        let cM : ℤ := ∑ e ∈ M, G.cost e
        (HasFactor (G.plus U) α ↔ HasFactor (auxGraph G α M f U) (auxBeta α f)) ∧
        (∀ F : Finset (Fin (auxGraph G α M f U).m), IsFactor (auxGraph G α M f U) (auxBeta α f) F →
          IsFactor (G.plus U) α (proj G α M f U F) ∧
          edgeCost (G.plus U) (proj G α M f U F) = cM + edgeCost (auxGraph G α M f U) F - delCost) ∧
        minFactorCost (G.plus U) α =
          ((cM - delCost : ℤ) : WithTop ℤ) + minFactorCost (auxGraph G α M f U) (auxBeta α f) := by sorry

end MatroidSensOracle.Supplement
