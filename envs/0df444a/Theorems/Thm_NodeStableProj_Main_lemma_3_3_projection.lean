-- Prove2me | Theorems.Thm_NodeStableProj_Main_lemma_3_3_projection
-- name    : NodeStableProj.Main.lemma_3_3_projection
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:58:57.483761+00:00
-- url     : https://prove2.me/theorems/c8b645b8-5485-48b3-9da5-1cf9ef69cc6b
-- title:
--   Lemma 3.3 item 1 — P_{D,D̂,ε̃} is a (D, D̂)-projection, and a.s. every omitted edge has an endpoint of output degree ≥ D
-- statement:
--   For all integers $0<D<\hat D$, every $\tilde\varepsilon>0$ and every fallback rule (any choice of a maximal $\hat D$-bounded subgraph), the algorithm $\mathcal P_{D,\hat D,\tilde\varepsilon}$ of Algorithm 1 is a $(D,\hat D)$-projection: for every graph $G$, with probability 1, its output $H$ is a $\hat D$-bounded subgraph of $G$ on $V(G)$, and $H=G$ when $G$ is $D$-bounded. Moreover, for every input $G$, with probability 1,
--   $$\{u,v\}\in E(G)\setminus E(H)\ \Longrightarrow\ \max\{\deg_H(u),\deg_H(v)\}\ge D. \tag{1}$$
--
--   Equation (1) is what keeps the projection from discarding too many edges (Proposition 3.4). Items 2 and 3 of Lemma 3.3 and its closing simplification are the companion items `lemma_3_3_efficiency`, `lemma_3_3_stability` and `lemma_3_3_simplification`.
--
--   Differences from the source:
--   - reading: Algorithm 1 returns "any maximal D̂-bounded subgraph" → the statement holds for every fallback rule F with IsFallbackRule D̂ F; reason: the stronger reading: the result must hold whichever subgraph is returned
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 11, Lemma 3.3 item 1 and Equation (1)

import Mathlib
import Definitions.Def_NodeStableProj_Main_Stability
import Definitions.Def_NodeStableProj_Main_Projection

open MeasureTheory

namespace NodeStableProj.Main

/-- Lemma 3.3, item 1 (Projection), p. 11: for `0 < D < D̂`, `ε̃ > 0` and every fallback rule,
`P_{D,D̂,ε̃}` is a `(D, D̂)`-projection, and for every input `G`, with probability 1, every edge of
`G` omitted from the output `H` has an endpoint of `H`-degree at least `D` (Equation (1)). -/
theorem lemma_3_3_projection (D Dhat : ℕ) (εt : ℝ) (hD : 0 < D) (hDD : D < Dhat)
    (hεt : 0 < εt) (F : Graph → Graph) (hF : IsFallbackRule Dhat F) :
    IsProjection D Dhat (alg1Law D Dhat εt F) ∧
      ∀ G : Graph, ∀ᵐ H ∂(alg1Law D Dhat εt F G), G.EdgePreserving D H := by sorry

end NodeStableProj.Main
