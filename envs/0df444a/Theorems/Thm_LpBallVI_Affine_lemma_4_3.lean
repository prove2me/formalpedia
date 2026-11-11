-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_3
-- name    : LpBallVI.Affine.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:02.601574+00:00
-- url     : https://prove2.me/theorems/26a9af23-4e78-4c1a-ad75-187161003cf6
-- title:
--   Lemma 4.3 — σ_λ is odd, increasing, 1-Lipschitz, |σ_λ(t)| ≤ |t|, strictly convex (p < 2) or concave (p > 2) on (0, ∞)
-- statement:
--   Let $1 < p < \infty$, $p \ne 2$, $\lambda > 0$, and $\sigma_\lambda = h_\lambda^{-1}$ with $h_\lambda(t) = t + \lambda|t|^{p-2}t$. Then $\sigma_\lambda$ is odd, increasing and 1-Lipschitz, and
--   $$|\sigma_\lambda(t)| \le |t| \quad (t \in \mathbb R);$$
--   moreover $\sigma_\lambda$ is strictly convex on $(0,\infty)$ when $1 < p < 2$ and strictly concave on $(0, \infty)$ when $p > 2$. The curvature is what the reduction exploits; for $p = 2$, $\sigma_\lambda$ is linear.
--
--   Differences from the source:
--   - reading: σ_λ is increasing → σ_λ is strictly increasing (StrictMono); reason: h_λ is strictly increasing (Lemma 4.2), so its inverse is; the stronger reading
--   - encoding: σ_λ = h_λ^{−1} → σ_λ(t) = sup{u : h_λ(u) ≤ t}; reason: equals the inverse for p > 1, λ > 0 (Lemma 4.2)
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 20, Lemma 4.3

import Mathlib
import Definitions.Def_LpBallVI_Affine_Sigma

namespace LpBallVI.Affine

/-- **Lemma 4.3**, p. 20: for `1 < p < ∞`, `p ≠ 2`, `λ > 0`, the inverse mapping `σ_λ` is odd,
increasing and 1-Lipschitz, `|σ_λ(t)| ≤ |t|`, strictly convex on `(0, ∞)` when `p < 2` and strictly
concave on `(0, ∞)` when `p > 2`. -/
theorem lemma_4_3 (p lam : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (hlam : 0 < lam) :
    (∀ t, sigmaLam p lam (-t) = -sigmaLam p lam t) ∧
      StrictMono (sigmaLam p lam) ∧
      (∀ s t, |sigmaLam p lam s - sigmaLam p lam t| ≤ |s - t|) ∧
      (∀ t, |sigmaLam p lam t| ≤ |t|) ∧
      (p < 2 → StrictConvexOn ℝ (Set.Ioi 0) (sigmaLam p lam)) ∧
      (2 < p → StrictConcaveOn ℝ (Set.Ioi 0) (sigmaLam p lam)) := by sorry

end LpBallVI.Affine
