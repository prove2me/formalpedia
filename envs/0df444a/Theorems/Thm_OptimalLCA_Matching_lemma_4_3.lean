-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_4_3
-- name    : OptimalLCA.Matching.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:20.559195+00:00
-- url     : https://prove2.me/theorems/1d24e0dc-0f43-4882-881b-13394e1051ad
-- title:
--   Lemma 4.3 — R_α is convex and 1/3-area convex for α ≥ 10; inequality (4.7)
-- statement:
--   For $\alpha\ge10$, the regularizer $R_\alpha(x,q)=2\sum_v(1+\ell_v(q))\psi(x_v)+\alpha H(q)$ is convex on $Z$ and $\tfrac13$-area convex for $g$ (Definition 4.1). Moreover, for every interior $z\in(-1,1)^V\times Q^\circ$ and all $z',z^+\in Z$,
--   $$\tfrac13\langle g(z')-g(z),z'-z^+\rangle\le D^\alpha_z(z')+D^\alpha_z(z^+).\tag{4.7}$$
--   This is the inequality the extragradient analysis of §5 uses.
--
--   Differences from the source:
--   - encoding: ∇R_α(z) in the Bregman divergence → fderiv of the formula of R_α on ℝ^V × ℝ^I at the interior base z; reason: the formula is differentiable there and its gradient is (4.6); the block constants vanish against w − z
--   - encoding: interior z → z ∈ (−1, 1)^V × Q° (all proposal probabilities positive); reason: the paper's definition of an interior base (p. 18)
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 19, Lemma 4.3, (4.7)

import Mathlib
import Definitions.Def_OptimalLCA_Matching_SaddlePoint

namespace OptimalLCA.Matching

/-- Lemma 4.3 (area convexity of `R_α`). For `α ≥ 10`, `R_α` is convex on `Z` and
`⅓`-area convex for `g`; moreover, for every interior `z` and all `z', z⁺ ∈ Z`,
`⅓ ⟨g(z') - g(z), z' - z⁺⟩ ≤ D^α_z(z') + D^α_z(z⁺)` (4.7). -/
theorem lemma_4_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (α : ℝ) (hα : 10 ≤ α) :
    ConvexOn ℝ {z | InZ G z} (regR G Finset.univ α) ∧
    IsAreaConvex G (1 / 3) (regR G Finset.univ α) ∧
    ∀ z z' zp : StateSpace G, IsInteriorBase G z → InZ G z' → InZ G zp →
      (1 / 3 : ℝ) * ip G (gOp G z' - gOp G z) (z' - zp) ≤
        bregman G Finset.univ α z z' + bregman G Finset.univ α z zp := by sorry

end OptimalLCA.Matching
