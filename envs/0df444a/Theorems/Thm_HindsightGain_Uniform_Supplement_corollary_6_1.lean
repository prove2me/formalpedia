-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_corollary_6_1
-- name    : HindsightGain.Uniform.Supplement.corollary_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:21.324605+00:00
-- url     : https://prove2.me/theorems/fe3c012b-3e30-499e-826d-82790b75e903
-- title:
--   Corollary 6.1 — Zhao's question: max-cut fraction error $C(p_N\rho_N)^{-1/4}$
-- statement:
--   Let $C$ be a constant for which Theorem 11 holds. Let $(G_N)$ be graphs with $e(G_N)\ge1$, let $\rho_N=e(G_N)/v(G_N)$, and let $p_N\in(0,1]$ satisfy $p_N\rho_N\to\infty$. Then, with probability tending to one, $H_N=G_N[S_{p_N}]$ has an edge and
--   $$\Big|\frac{\mathrm{mc}(H_N)}{e(H_N)}-\frac{\mathrm{mc}(G_N)}{e(G_N)}\Big|\le C(p_N\rho_N)^{-1/4}.$$
--   In particular, for $p_N=\tfrac12$ and $\rho_N\to\infty$, the max-cut fraction is preserved with probability tending to one: $\mathbb P(e(H_N)\ge1)\to1$ and, for every $\eta>0$, the probability that $e(H_N)\ge1$ and the two fractions differ by at most $\eta$ tends to one.
--
--   This answers Zhao's question on one-half vertex percolation.
--
--   Differences from the source:
--   - reading: C is the constant of Theorem 11 → C is any real satisfying the full conclusion of Theorem 11 (written out as a hypothesis); reason: the corollary holds with every admissible constant of Theorem 11
--   - encoding: graphs G_N → graphs on Fin (n N) with varying vertex counts, each N with its own sampling law; reason: no coupling across N is needed for statements about probabilities
--   - encoding: the induced subgraph G[S] → the graph on the same vertex set with the vertices outside S isolated; reason: it has exactly the edges and cuts of G[S]
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
--   - reading: with probability tending to one H_N has an edge, and mc(H_N)/e(H_N) − mc(G_N)/e(G_N) → 0 in probability → P(e(H_N) ≥ 1) → 1 and, for every η > 0, P(e(H_N) ≥ 1 and |difference| ≤ η) → 1; reason: the ratio is undefined on edgeless samples; once P(e(H_N) ≥ 1) → 1 the joint form is equivalent to convergence in probability
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Corollary 6.1, pp.27-28

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_graphs

set_option autoImplicit false
open Filter Topology

namespace HindsightGain.Uniform.Supplement

/-- Corollary 6.1, pp.27-28. "`C` is the constant of Theorem 11" is the hypothesis that `C` is an
admissible constant in Theorem 11 (written out in full). Sequences may have varying vertex sets
`Fin (n N)`; each `N` uses its own sampling law. The second clause is the `p_N = 1/2`
specialization. -/
theorem corollary_6_1 (C : ℝ)
    (hC : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (p δ : ℝ),
      1 ≤ edgeCount G → 0 < p → p ≤ 1 → 0 < δ → δ < 1 → 24 / δ ≤ p * density G →
      1 - δ ≤ bernProb (fun _ : Fin n => p) (fun S =>
        p ^ 2 * (edgeCount G : ℝ) / 2 ≤ (edgeCount (induced G S) : ℝ) ∧
        0 < edgeCount (induced G S) ∧
        |cutFraction (induced G S) - cutFraction G| ≤
          C * Real.sqrt ((1 - p) / (δ * p * density G)) ∧
        |(maxCut (induced G S) : ℝ) / (p ^ 2 * (maxCut G : ℝ)) - 1| ≤
          C * Real.sqrt ((1 - p) / (δ * p * density G)))) :
    (∀ (n : ℕ → ℕ) (G : (N : ℕ) → SimpleGraph (Fin (n N))) (p : ℕ → ℝ),
      (∀ N, 1 ≤ edgeCount (G N)) → (∀ N, 0 < p N ∧ p N ≤ 1) →
      Tendsto (fun N => p N * density (G N)) atTop atTop →
      Tendsto (fun N => bernProb (fun _ : Fin (n N) => p N) (fun S =>
          1 ≤ edgeCount (induced (G N) S) ∧
          |cutFraction (induced (G N) S) - cutFraction (G N)| ≤
            C * (p N * density (G N)) ^ (-(1 : ℝ) / 4))) atTop (𝓝 1)) ∧
    (∀ (n : ℕ → ℕ) (G : (N : ℕ) → SimpleGraph (Fin (n N))),
      (∀ N, 1 ≤ edgeCount (G N)) →
      Tendsto (fun N => density (G N)) atTop atTop →
      CutFractionPreserved n G (fun _ => 1 / 2)) := by sorry

end HindsightGain.Uniform.Supplement
