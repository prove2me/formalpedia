-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_lemma_4_1
-- name    : ImprovedSteinerForest.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:29:27.928544+00:00
-- url     : https://prove2.me/theorems/ba821c1f-e8df-4f8e-a035-71789a8e1d32
-- title:
--   Lemma 4.1 — c(T₀) ≤ 2Σ_U y_U and gain(𝒮) = c(T₀) − mst(T₀/𝒮) for every actively connected collection
-- statement:
--   Let $I$ be a feasible Steiner Forest instance, $\varepsilon>0$ rational, and $R$ the extended growth run with parameter $\varepsilon$, with auxiliary forest $T_0$. Then
--   $$c(T_0)\le 2\sum_U y_U,$$
--   and every actively connected collection $\mathcal S$ satisfies
--   $$\mathrm{gain}(\mathcal S)=c(T_0)-\mathrm{mst}(T_0/\mathcal S).\tag{4.1}$$
--
--   The identity turns the gain, an integral over the growth history, into a spanning-tree saving in a graph that contains both input edges and auxiliary edges; the rounding routine of §4 works in that graph.
--
--   Differences from the source:
--   - generalization: finite undirected network → multigraph edge list on `Fin n` with loops, parallel edges and repeated labelled pairs; reason: contraction produces multigraphs (p. 13); a simple network is a special case.
--   - generalization: growth on the preprocessed graph of a call (zero-cost components contracted, satisfied demands removed, every cost positive, pp. 13–14) → growth run directly on any instance with nonnegative costs; reason: zero-cost edges are tight at time zero and merge in zero-duration steps; the preprocessed graph is a special case.
--   - generalization: the algorithm's growth history (ε = 6005367/10⁸, §3.3; actively connected collections are used "in the ε > 0 setting used here", p. 15) → the growth run for any rational ε > 0; reason: Lemma 4.1 states no condition on ε and its proof uses none; the algorithm's ε is a special case.
--   - encoding: the auxiliary forest and `mst(T₀/𝒮)` → `auxEdges` (one entry per merger and class) and the minimum cost of a set of auxiliary edges that, with the identifications of `𝒮`, connects every active class; reason: classes are disjoint and every auxiliary edge stays in its class, so this is the sum of the per-class minimum spanning trees.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 20, Lemma 4.1

import Mathlib
import Definitions.Def_ImprovedSteinerForest_Main_Instance
import Definitions.Def_ImprovedSteinerForest_Main_Growth
import Definitions.Def_ImprovedSteinerForest_Main_AuxForest

namespace ImprovedSteinerForest.Main

/-- Lemma 4.1 (p. 20): the auxiliary forest satisfies `c(T₀) ≤ 2 Σ_U y_U`, and every actively
connected collection satisfies `gain(𝒮) = c(T₀) − mst(T₀/𝒮)` (4.1). -/
theorem lemma_4_1 (ε : ℚ) (hε : 0 < ε) (I : Instance) (hI : I.IsFeasibleInst)
    (R : GrowthRun I) (hR : IsGrowthRun ε I R) :
    R.auxCost ≤ 2 * R.sumY ∧
      ∀ 𝒮 : Finset (Finset (Fin I.n)), R.IsActConnColl 𝒮 →
        R.gain 𝒮 = R.auxCost - R.mstMod 𝒮 := by sorry

end ImprovedSteinerForest.Main
