-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_7_2
-- name    : OptimalLCA.Matching.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:45:29.882368+00:00
-- url     : https://prove2.me/theorems/35bee7d1-9d1a-46fd-8a35-7c8e673d54f7
-- title:
--   Lemma 7.2 — relative clipping: (1 − 2/√K) min{1, ℓ} ≤ E min{K, N}/K ≤ min{1, ℓ}
-- statement:
--   If $N$ is a sum of independent Bernoulli variables with mean $K\ell$, for an integer $K\ge1$, then
--   $$\Big(1-\frac2{\sqrt K}\Big)\min\{1,\ell\}\le\frac{\mathbb E\min\{K,N\}}K\le\min\{1,\ell\}.$$
--   It bounds the loss from capping each vertex's incoming proposals at $K$ (Corollary 7.3).
--
--   Differences from the source:
--   - encoding: N a sum of independent Bernoulli variables → N = Σ_{i<m} X_i with X_i measurable, {0,1}-valued and mutually independent on a probability space; reason: finitely many summands, any biases
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 39, Lemma 7.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace OptimalLCA.Matching

/-- Lemma 7.2 (relative clipping). If `N` is a sum of independent Bernoulli variables with
mean `Kℓ`, for an integer `K ≥ 1`, then
`(1 - 2/√K) min{1, ℓ} ≤ E min{K, N} / K ≤ min{1, ℓ}`. -/
theorem lemma_7_2 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (m : ℕ) (X : Fin m → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hind : iIndepFun X)
    (K : ℕ) (hK : 1 ≤ K) (ℓ : ℝ) (hmean : ∫ ω, ∑ i, X i ω = (K : ℝ) * ℓ) :
    (1 - 2 / Real.sqrt K) * min 1 ℓ ≤ (∫ ω, min (K : ℝ) (∑ i, X i ω)) / K ∧
      (∫ ω, min (K : ℝ) (∑ i, X i ω)) / K ≤ min 1 ℓ := by sorry

end OptimalLCA.Matching
