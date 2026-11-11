-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_undirected_normalization
-- name    : MultiwayGap2325.Main.undirected_normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:05.611703+00:00
-- url     : https://prove2.me/theorems/5011dca7-4a81-4d0a-bc49-59644ccff2fb
-- title:
--   §1 — ordered edge aggregation preserves undirected CKR costs
-- statement:
--   Let $I$ be a finite graph represented by an ordered edge set. Form $\bar I$ by deleting loops and replacing all orientations of each unordered pair by one increasing pair with their summed weight. Every stored edge of $\bar I$ is increasing, and for every labeling $c$ and every real embedding $x$,
--   $$
--   \operatorname{cost}_{\bar I}(c)=\operatorname{cost}_I(c),\qquad
--   \operatorname{relax}_{\bar I}(x)=\operatorname{relax}_I(x).
--   $$
--   The integral optimum, fractional optimum and gap are therefore unchanged. This states the precise correspondence between the reused ordered-edge representation and the paper's undirected costs.
--
--   Differences from the source:
--   - encoding: an arbitrary finite undirected graph with distinct terminals → a graph on Fin n with Fin k terminals and an ordered edge list; reason: all finite vertex types admit reindexing; opposite orientations aggregate and loops have zero cost; neither n nor real weights are bounded
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), §1, p. 1, equations (1),(2)

import Definitions.Def_MultiwayGap2325_Main_FiniteGap

namespace MultiwayGap2325.Main

/-- Ordered edge pairs aggregate to the same undirected graph, §1, equations (1),(2). -/
theorem undirected_normalization {n k : ℕ}
    (I : MultiwayCut.Instance (Fin n) k) :
    (∀ e ∈ (normalize I).E, e.1 < e.2) ∧
    (∀ c : Fin n → Fin k,
      MultiwayCut.cutWeight (normalize I) c = MultiwayCut.cutWeight I c) ∧
    (∀ x : Fin n → Fin k → ℝ,
      MultiwayCut.relaxValue (normalize I) x = MultiwayCut.relaxValue I x) ∧
    integralOpt (normalize I) = integralOpt I ∧
    fractionalOpt (normalize I) = fractionalOpt I ∧
    instanceGap (normalize I) = instanceGap I := by sorry

end MultiwayGap2325.Main
