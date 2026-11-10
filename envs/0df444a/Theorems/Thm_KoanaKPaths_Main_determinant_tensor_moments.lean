-- Prove2me | Theorems.Thm_KoanaKPaths_Main_determinant_tensor_moments
-- name    : KoanaKPaths.Main.determinant_tensor_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:53.10479+00:00
-- url     : https://prove2.me/theorems/24df3a9d-809d-4c1b-94d9-2cb59f6a3d63
-- title:
--   Lemma 4 — determinant tensor moments
-- statement:
--   Let $n,k\ge1$, let $(c_\tau)_{\tau\in[n]^k}$ be a 0–1 coefficient tensor and $N=\sum_{\tau\ \text{multilinear}}c_\tau$ the sum over the words $\tau$ with pairwise distinct entries. Let $\sigma_{j,r}$ ($j\in[n]$, $r\in[k]$) be mutually independent uniform signs, $D_\tau=\det[\sigma_{\tau_1}\cdots\sigma_{\tau_k}]$ and $\Psi(\tau)=c_\tau D_\tau$. Then
--   $$\mathbb E\bigl(\|\Psi\|_F^2\bigr)=k!\,N\qquad\text{and}\qquad\mathbb E\bigl(\|\Psi\|_F^4\bigr)\le (k!)^2\,k^3\,N^2 .$$
--
--   So $\|\Psi\|_F^2/k!$ is an unbiased estimator of $N$ whose relative second moment is polynomial in $k$; this is the estimator of extensor-coding that the later sketches compress.
--
--   **Formalization Note** The expectation is the average over all $2^{nk}$ label bit patterns. $\|\Psi\|_F^4$ is $(\|\Psi\|_F^2)^2$.
--
--   Differences from the source:
--   - generalization: the coefficient tensor of the fixed circuit polynomial P in the Section 3 setup, where N > 0 is assumed for the analysis → every homogeneous degree-k 0–1 tensor over [n]^k, including N = 0; reason: every such tensor has a homogeneous 0–1 right-skew circuit, so all source instances are included; when N = 0 all supported words repeat a variable, hence Ψ and every sketch vanish
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 6 (PDF p. 7), Lemma 4

import Mathlib
import Definitions.Def_KoanaKPaths_Main_Estimator

namespace KoanaKPaths.Main

/-- **Lemma 4** (Koana, STOC 2027 submission #953, printed p. 6 / PDF p. 7).
`E(‖Ψ‖_F²) = k! N` and `E(‖Ψ‖_F⁴) ≤ (k!)² k³ N²`, the expectation over the independent uniform
label signs `σ_{j,r}`, for every homogeneous degree-`k` 0–1 coefficient tensor `c` over `n`
variables, `N = ∑_{τ multilinear} c_τ`. -/
theorem determinant_tensor_moments (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c) :
    uniformMean (fun σ : Labels n k => (psiFrobSq c σ : ℝ)) =
        (Nat.factorial k : ℝ) * (tensorN c : ℝ) ∧
      uniformMean (fun σ : Labels n k => ((psiFrobSq c σ : ℝ)) ^ 2) ≤
        (Nat.factorial k : ℝ) ^ 2 * (k : ℝ) ^ 3 * (tensorN c : ℝ) ^ 2 := by sorry

end KoanaKPaths.Main
