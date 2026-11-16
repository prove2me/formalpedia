-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_A_3
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:08:23.490185+00:00
-- url     : https://prove2.me/theorems/d9404ba1-11e9-461d-859e-0cd2e115022d
-- title:
--   Lemma A.3 — absolute-value vector contraction
-- statement:
--   Let $k\ge1$ and $m\ge0$ be integers. Let $T\subseteq(\mathbb R^m)^k$ be compact and contain zero. Suppose $L_0\ge0$ and $\phi:\mathbb R^m\to\mathbb R$ satisfy $\phi(0)=0$ and $|\phi(u)-\phi(w)|\le L_0\|u-w\|_2$ for all $u,w$. For independent uniform signs $\tau_i$ and $\sigma_{i\ell}$,
--   $$\mathbb E_\tau\max_{t\in T}\left|\frac1k\sum_i\tau_i\phi(t_i)\right|\le2\sqrt2L_0\,\mathbb E_\sigma\max_{t\in T}\left|\frac1k\sum_i\sum_\ell\sigma_{i\ell}t_{i\ell}\right|.$$
--   Both maxima contain absolute values. The norm on each $t_i$ is Euclidean, represented by EuclideanSpace rather than the sup norm on a function type. This is the absolute-value contraction tool required for the r-way signed reduction; the zero-dimensional case also satisfies the displayed formula.
--
--   Differences from the source:
--   - encoding: expectations over independent uniform signs → uniform finite sums over Boolean sign vectors or matrices; reason: false denotes +1 and true denotes -1; each sign assignment receives its exact uniform probability
--   - encoding: Euclidean vectors, a nonnegative Lipschitz constant, and attained compact maxima → EuclideanSpace, explicit L₀ ≥ 0, and real sSup on the same compact images; reason: these make the norm and the conventional Lipschitz-constant domain explicit without changing the inequality
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma A.3, p. 34. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_A_3 (k m : ℕ) (hk : 1 ≤ k)
    (T : Set (Fin k → EuclideanSpace ℝ (Fin m))) (hT : IsCompact T) (hzero : 0 ∈ T)
    (φ : EuclideanSpace ℝ (Fin m) → ℝ) (L₀ : ℝ) (hL : 0 ≤ L₀)
    (hφ : ∀ u w, |φ u - φ w| ≤ L₀ * ‖u - w‖) (hφ0 : φ 0 = 0) :
    signAverage k (fun τ => sSup ((fun t =>
      |(∑ i, signValue (τ i) * φ (t i)) / (k : ℝ)|) '' T)) ≤
    2 * Real.sqrt 2 * L₀ * matrixSignAverage k m (fun σ =>
      sSup ((fun t => |(∑ i, ∑ l, signValue (σ i l) * (t i) l) / (k : ℝ)|) '' T)) := by sorry

end MaxCutSample2027.Coreset.Supplement
