-- Prove2me | Theorems.Thm_KoanaKPaths_Main_recursive_estimator_moments
-- name    : KoanaKPaths.Main.recursive_estimator_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:53.928514+00:00
-- url     : https://prove2.me/theorems/954b8c2f-a5f4-4d0d-acb9-03c60fba50ce
-- title:
--   Lemma 6 — recursive estimator moments
-- statement:
--   Let $n,k,\ell\ge1$, let $(c_\tau)_{\tau\in[n]^k}$ be a 0–1 coefficient tensor with $N=\sum_{\tau\ \text{multilinear}}c_\tau$, and let $\Psi=S_0,S_1,\dots,S_k$ be the recursive sign sketches of width $\ell$ built from independent uniform label signs $\sigma_{j,r}$ and independent uniform sign matrices $R_1,\dots,R_k$ (Section 3.1). For $0\le i\le k$ let
--   $$Y_i=\frac{\|S_i\|_F^2}{\ell^i\,k!}.$$
--   Then
--   $$\mathbb E(Y_i)=N\qquad\text{and}\qquad\mathbb E(Y_i^2)\le\Bigl(1+\frac2\ell\Bigr)^{i}k^3N^2 .$$
--   In particular, for $\ell=k$ the random variable $Y=Y_k=\|S_k\|_2^2/(k^k\,k!)$ satisfies $\mathbb E(Y)=N$ and $\mathbb E(Y^2)\le e^2k^3N^2$.
--
--   With $\ell=k$, $Y$ is an unbiased estimator of $N$ with relative second moment at most $e^2k^3$, which is what the median-of-means amplification of the algorithm needs.
--
--   **Formalization Note** The expectation is the average over all label bits and all sign-matrix bits. For $i=k$ the residual word is empty, so $\|S_k\|_F^2=\|S_k\|_2^2=\sum_{a\in[\ell]}S_k(a)^2$.
--
--   Differences from the source:
--   - generalization: the coefficient tensor of the fixed circuit polynomial P in the Section 3 setup, where N > 0 is assumed for the analysis → every homogeneous degree-k 0–1 tensor over [n]^k, including N = 0; reason: every such tensor has a homogeneous 0–1 right-skew circuit, so all source instances are included; when N = 0 all supported words repeat a variable, hence Ψ and every sketch vanish
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 8 (PDF p. 9), Lemma 6

import Mathlib
import Definitions.Def_KoanaKPaths_Main_Estimator

namespace KoanaKPaths.Main

/-- **Lemma 6** (Koana, STOC 2027 submission #953, printed p. 8 / PDF p. 9).
For every sketch width `ℓ ≥ 1` and `0 ≤ i ≤ k`, `Y_i = ‖S_i‖_F² / (ℓ^i k!)` satisfies
`E(Y_i) = N` and `E(Y_i²) ≤ (1 + 2/ℓ)^i k³ N²`, the expectation over the independent uniform
labels `σ` and sign matrices `R₁, …, R_k`. In particular, for `ℓ = k`,
`Y = Y_k = ‖S_k‖₂² / (k^k k!)` satisfies `E(Y) = N` and `E(Y²) ≤ e² k³ N²`. -/
theorem recursive_estimator_moments (n k ℓ : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ)
    (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c) :
    (∀ i ≤ k,
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => Yhat c i ω.1 ω.2) = (tensorN c : ℝ) ∧
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => (Yhat c i ω.1 ω.2) ^ 2) ≤
        (1 + 2 / (ℓ : ℝ)) ^ i * (k : ℝ) ^ 3 * (tensorN c : ℝ) ^ 2) ∧
    (ℓ = k →
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => Yhat c k ω.1 ω.2) = (tensorN c : ℝ) ∧
      uniformMean (fun ω : Labels n k × SketchSigns n k ℓ => (Yhat c k ω.1 ω.2) ^ 2) ≤
        Real.exp 2 * (k : ℝ) ^ 3 * (tensorN c : ℝ) ^ 2) := by sorry

end KoanaKPaths.Main
