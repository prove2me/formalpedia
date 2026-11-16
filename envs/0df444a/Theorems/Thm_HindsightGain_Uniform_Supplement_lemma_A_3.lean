-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_lemma_A_3
-- name    : HindsightGain.Uniform.Supplement.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:04:36.540208+00:00
-- url     : https://prove2.me/theorems/81569cfb-c99d-4b40-b628-831fb46aa007
-- title:
--   Lemma A.3 — Counting even subgraphs: at most $(2\sqrt{2t})^k$ with $k$ edges
-- statement:
--   Let $G$ be a finite simple graph with $t\ge1$ edges. Then $G$ has no nonempty even edge set with fewer than three edges, and for every $k\ge3$ the number of even edge sets $J\subseteq E(G)$ with exactly $k$ edges is at most
--   $$\big(2\sqrt{2t}\big)^k .$$
--   An edge set is even if every vertex has even degree in it.
--
--   Combined with Lemma A.2 this bounds the $\chi^2$-divergence of any fixed small query set.
--
--   Differences from the source:
--   - reading: even subgraphs with exactly k edges → even edge subsets J ⊆ E(G) with |J| = k; reason: a subgraph is determined by its edge set here, as in the proof (even sets are counted)
--   - encoding: a simple graph → a Mathlib simple graph on an arbitrary finite vertex type; reason: finite simple graphs
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma A.3, p.34

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_planted

set_option autoImplicit false
open Classical

namespace HindsightGain.Uniform.Supplement

/-- Lemma A.3, p.34: a finite simple graph with `t ≥ 1` edges has no nonempty even edge set with
fewer than three edges, and at most `(2√(2t))^k` even edge sets with exactly `k` edges, `k ≥ 3`. -/
theorem lemma_A_3 {V : Type} [Fintype V] (G : SimpleGraph V) (ht : 1 ≤ edgeCount G) :
    (∀ J ⊆ edgeFinset' G, J.Nonempty → IsEvenEdgeSet J → 3 ≤ J.card) ∧
    ∀ k : ℕ, 3 ≤ k →
      ((((edgeFinset' G).powerset.filter (fun J => IsEvenEdgeSet J ∧ J.card = k)).card : ℝ) ≤
        (2 * Real.sqrt (2 * (edgeCount G : ℝ))) ^ k) := by sorry

end HindsightGain.Uniform.Supplement
