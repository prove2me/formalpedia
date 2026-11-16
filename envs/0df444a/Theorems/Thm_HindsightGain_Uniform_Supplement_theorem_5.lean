-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_5
-- name    : HindsightGain.Uniform.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:58:33.03239+00:00
-- url     : https://prove2.me/theorems/c70f825b-7240-4e42-9c0e-968a6f3713dd
-- title:
--   Theorem 5 — Max-cut under vertex percolation: preserved iff $p\rho\to\infty$ (sharp)
-- statement:
--   Let $(G_N)$ be graphs with $e(G_N)\ge1$, let $\rho_N=e(G_N)/v(G_N)$, and let $p_N\in(0,1]$. If $p_N\rho_N\to\infty$, then with probability tending to one the random induced subgraph $H_N=G_N[S_{p_N}]$ has at least one edge, and
--   $$\frac{\mathrm{mc}(H_N)}{e(H_N)}-\frac{\mathrm{mc}(G_N)}{e(G_N)}\longrightarrow0\quad\text{in probability.}$$
--   Conversely, for every constant $c>0$ there are graphs $G_N$ with $e(G_N)\ge1$ and $\rho_N\to\infty$, and probabilities $p_N\in(0,1]$ with $p_N\rho_N=c$, for which this conclusion fails.
--
--   Taking $p_N=\tfrac12$ answers Zhao's question for every sequence with $\rho_N\to\infty$.
--
--   Differences from the source:
--   - encoding: graphs G_N → graphs on Fin (n N) with varying vertex counts, each N with its own sampling law; reason: no coupling across N is needed for statements about probabilities
--   - encoding: the induced subgraph G[S] → the graph on the same vertex set with the vertices outside S isolated; reason: it has exactly the edges and cuts of G[S]
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
--   - reading: with probability tending to one H_N has an edge, and mc(H_N)/e(H_N) − mc(G_N)/e(G_N) → 0 in probability → P(e(H_N) ≥ 1) → 1 and, for every η > 0, P(e(H_N) ≥ 1 and |difference| ≤ η) → 1; reason: the ratio is undefined on edgeless samples; once P(e(H_N) ≥ 1) → 1 the joint form is equivalent to convergence in probability
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 5, pp.7-8; proved by Corollary 6.1 and Proposition 6.2, pp.27-28

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_graphs

set_option autoImplicit false
open Filter Topology

namespace HindsightGain.Uniform.Supplement

/-- Theorem 5, pp.7-8: the forward direction for every sequence with `e(G_N) ≥ 1`,
`p_N ∈ (0,1]` and `p_N ρ_N → ∞`, and the converse for every real `c > 0`. -/
theorem theorem_5 :
    (∀ (n : ℕ → ℕ) (G : (N : ℕ) → SimpleGraph (Fin (n N))) (p : ℕ → ℝ),
      (∀ N, 1 ≤ edgeCount (G N)) → (∀ N, 0 < p N ∧ p N ≤ 1) →
      Tendsto (fun N => p N * density (G N)) atTop atTop →
      CutFractionPreserved n G p) ∧
    ∀ c : ℝ, 0 < c →
      ∃ (n : ℕ → ℕ) (G : (N : ℕ) → SimpleGraph (Fin (n N))) (p : ℕ → ℝ),
        (∀ N, 1 ≤ edgeCount (G N)) ∧ (∀ N, 0 < p N ∧ p N ≤ 1) ∧
        Tendsto (fun N => density (G N)) atTop atTop ∧
        (∀ N, p N * density (G N) = c) ∧
        ¬ CutFractionPreserved n G p := by sorry

end HindsightGain.Uniform.Supplement
