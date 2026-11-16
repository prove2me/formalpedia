-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_corollary_5_4
-- name    : HindsightGain.Uniform.Supplement.corollary_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:55:41.212907+00:00
-- url     : https://prove2.me/theorems/3d3f68d3-4658-4cd0-a92e-0a3649359ccd
-- title:
--   Corollary 5.4 — Graph estimator for $\mathrm{mc}$ and $\beta$ with joint success $3/4$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every $\varepsilon\in(0,1)$. Let $G$ be a graph on $n\ge1$ vertices, let $q=\min\{n,C\varepsilon^{-2}\}$ and $p=q/n$, and sample $S=S_p$. If $|S|>4q$, output $0$ (for both); otherwise query all pairs inside $S$ and output $\widehat{\mathrm{mc}}=p^{-2}\mathrm{mc}(G[S])$ and $\hat\beta=p^{-2}\beta(G[S])$. Then:
--   1. with probability at least $3/4$, $|\widehat{\mathrm{mc}}-\mathrm{mc}(G)|\le\varepsilon n^2$ and $|\hat\beta-\beta(G)|\le\varepsilon n^2$ simultaneously;
--   2. on every sample the algorithm examines at most $4q$ vertices and makes fewer than $8q^2$ queries;
--   3. the algorithm is nonadaptive: its queries depend only on $S$, and its outputs depend on $G$ only through the answers to those queries.
--
--   This is the upper bound of Theorem 4(a).
--
--   Differences from the source:
--   - encoding: an n-vertex graph → a Mathlib simple graph on Fin n; reason: finite simple graphs up to relabeling
--   - encoding: the induced subgraph G[S] → the graph on the same vertex set with the vertices outside S isolated; reason: it has exactly the edges and cuts of G[S]
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
--   - reading: an absolute constant C → an absolute constant C > 0; reason: q = min{n, Cε^{−2}} must be a positive sample size
--   - encoding: the algorithm is nonadaptive → queries determined by S alone and outputs equal for any two graphs agreeing on the queried pairs; reason: this is the definition of nonadaptivity for this estimator
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Corollary 5.4, p.26

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_queries

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

/-- Corollary 5.4, p.26: one absolute `C > 0`; `q = min{n, Cε^{-2}}`, `p = q/n`, `S = S_p`. With
probability at least `3/4` both outputs are within `εn²`; the outputs depend only on the answers
to the queries, which are fixed by `S` alone (nonadaptive); every run examines at most `4q`
vertices and makes fewer than `8q²` queries. -/
theorem corollary_5_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε < 1 → ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 1 ≤ n →
      3 / 4 ≤ bernProb (fun _ : Fin n => min (n : ℝ) (C * (ε⁻¹) ^ 2) / n) (fun S =>
          |estMc G (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S - (maxCut G : ℝ)| ≤ ε * (n : ℝ) ^ 2 ∧
          |estBeta G (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S - bipDist G| ≤ ε * (n : ℝ) ^ 2) ∧
        (∀ S : Finset (Fin n),
          ((examined (estQueries (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S)).card : ℝ) ≤
              4 * min (n : ℝ) (C * (ε⁻¹) ^ 2) ∧
          ((estQueries (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S).card : ℝ) <
              8 * (min (n : ℝ) (C * (ε⁻¹) ^ 2)) ^ 2) ∧
        (∀ (G' : SimpleGraph (Fin n)) (S : Finset (Fin n)),
          (∀ z ∈ estQueries (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S, answers G z = answers G' z) →
          estMc G (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S = estMc G' (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S ∧
          estBeta G (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S =
            estBeta G' (min (n : ℝ) (C * (ε⁻¹) ^ 2)) S) := by sorry

end HindsightGain.Uniform.Supplement
