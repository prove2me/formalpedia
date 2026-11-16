-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_11
-- name    : HindsightGain.Uniform.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:27.411449+00:00
-- url     : https://prove2.me/theorems/5febe8dc-447a-4bb1-9735-2432c1f8fdf4
-- title:
--   Theorem 11 — Quantitative vertex percolation: three estimates on one event
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a graph with $n$ vertices and $m\ge1$ edges, let $\rho=m/n$, and let $p\in(0,1]$ and $\delta\in(0,1)$ satisfy $p\rho\ge24/\delta$. Then, with probability at least $1-\delta$, the graph $H=G[S_p]$ satisfies simultaneously $e(H)\ge\tfrac12p^2m>0$,
--   $$\Big|\frac{\mathrm{mc}(H)}{e(H)}-\frac{\mathrm{mc}(G)}{e(G)}\Big|\le C\sqrt{\frac{1-p}{\delta p\rho}}\qquad\text{and}\qquad\Big|\frac{\mathrm{mc}(H)}{p^2\,\mathrm{mc}(G)}-1\Big|\le C\sqrt{\frac{1-p}{\delta p\rho}}.$$
--
--   The second estimate is a multiplicative guarantee for the rescaled sampled max-cut; the first answers Zhao's question quantitatively.
--
--   Differences from the source:
--   - encoding: an n-vertex graph → a Mathlib simple graph on Fin n; reason: finite simple graphs up to relabeling
--   - encoding: the induced subgraph G[S] → the graph on the same vertex set with the vertices outside S isolated; reason: it has exactly the edges and cuts of G[S]
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 11, p.27

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_graphs

set_option autoImplicit false

namespace HindsightGain.Uniform.Supplement

/-- Theorem 11, p.27: one absolute constant `C`; for every finite simple graph on `n` vertices with
`m ≥ 1` edges, `ρ = m/n`, `p ∈ (0,1]`, `δ ∈ (0,1)` and `pρ ≥ 24/δ`, all three assertions hold on
one event of probability at least `1 - δ` for `H = G[S_p]`. -/
theorem theorem_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (p δ : ℝ),
      1 ≤ edgeCount G → 0 < p → p ≤ 1 → 0 < δ → δ < 1 → 24 / δ ≤ p * density G →
      1 - δ ≤ bernProb (fun _ : Fin n => p) (fun S =>
        p ^ 2 * (edgeCount G : ℝ) / 2 ≤ (edgeCount (induced G S) : ℝ) ∧
        0 < edgeCount (induced G S) ∧
        |cutFraction (induced G S) - cutFraction G| ≤
          C * Real.sqrt ((1 - p) / (δ * p * density G)) ∧
        |(maxCut (induced G S) : ℝ) / (p ^ 2 * (maxCut G : ℝ)) - 1| ≤
          C * Real.sqrt ((1 - p) / (δ * p * density G))) := by sorry

end HindsightGain.Uniform.Supplement
