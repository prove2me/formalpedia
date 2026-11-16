-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_proposition_6_2
-- name    : HindsightGain.Uniform.Supplement.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:57.735774+00:00
-- url     : https://prove2.me/theorems/5447258c-d42d-4ffd-b862-91b0b2b992c4
-- title:
--   Proposition 6.2 — Sharpness of the density condition $p\rho\to\infty$
-- statement:
--   For every $c>0$ there are graphs $G_N$ with $e(G_N)\ge1$ and $\rho_N=e(G_N)/v(G_N)\to\infty$, and probabilities $p_N\in(0,1]$ with $p_N\rho_N=c$, such that
--   1. there is $\kappa>0$ with $\mathbb P\big(e(G_N[S_{p_N}])\le1\big)\ge\kappa$ for every $N$;
--   2. $\mathrm{mc}(G_N)/e(G_N)\to\tfrac12$;
--   3. the max-cut fraction of $G_N$ is not preserved with probability tending to one: it is not true that for every $\eta>0$, $\mathbb P\big(e(H_N)\ge1$ and $|\mathrm{mc}(H_N)/e(H_N)-\mathrm{mc}(G_N)/e(G_N)|\le\eta\big)\to1$, where $H_N=G_N[S_{p_N}]$.
--
--   This is the converse half of Theorem 5.
--
--   Differences from the source:
--   - encoding: graphs G_N → graphs on Fin (n N) with varying vertex counts, each N with its own sampling law; reason: no coupling across N is needed for statements about probabilities
--   - encoding: the induced subgraph G[S] → the graph on the same vertex set with the vertices outside S isolated; reason: it has exactly the edges and cuts of G[S]
--   - encoding: probability and expectation over the random retained set → exact finite sums over all subsets weighted by ∏_{i∈S}p_i∏_{i∉S}(1−p_i); reason: this is the law of the random set; no instance changes
--   - reading: with probability bounded away from zero → a single κ > 0 bounding the probability below for every N; reason: the uniform-in-N reading of bounded away from zero
--   - reading: not preserved with probability tending to one → the negation of: for every η > 0, P(e(H_N) ≥ 1 and |difference| ≤ η) → 1; reason: the joint form of the conclusion of Theorem 5, as in its formalization
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Proposition 6.2, p.28

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_graphs

set_option autoImplicit false
open Filter Topology

namespace HindsightGain.Uniform.Supplement

/-- Proposition 6.2, p.28: for every `c > 0`, graphs `G_N` (on `Fin (n N)`) with `ρ_N → ∞` and
`p_N ∈ (0,1]` with `p_N ρ_N = c`, such that `P(e(G_N[S_{p_N}]) ≤ 1)` is bounded below by a positive
constant for all `N`, `mc(G_N)/e(G_N) → 1/2`, and the max-cut fraction is not preserved with
probability tending to one. -/
theorem proposition_6_2 (c : ℝ) (hc : 0 < c) :
    ∃ (n : ℕ → ℕ) (G : (N : ℕ) → SimpleGraph (Fin (n N))) (p : ℕ → ℝ),
      (∀ N, 1 ≤ edgeCount (G N)) ∧ (∀ N, 0 < p N ∧ p N ≤ 1) ∧
      Tendsto (fun N => density (G N)) atTop atTop ∧
      (∀ N, p N * density (G N) = c) ∧
      (∃ κ : ℝ, 0 < κ ∧ ∀ N, κ ≤ bernProb (fun _ : Fin (n N) => p N)
        (fun S => edgeCount (induced (G N) S) ≤ 1)) ∧
      Tendsto (fun N => cutFraction (G N)) atTop (𝓝 (1 / 2)) ∧
      ¬ (∀ η : ℝ, 0 < η → Tendsto (fun N => bernProb (fun _ : Fin (n N) => p N)
        (fun S => 1 ≤ edgeCount (induced (G N) S) ∧
          |cutFraction (induced (G N) S) - cutFraction (G N)| ≤ η)) atTop (𝓝 1)) := by sorry

end HindsightGain.Uniform.Supplement
