-- Prove2me | Theorems.Thm_GaussianMatrix_pinv_spectral_tail
-- name    : GaussianMatrix.pinv_spectral_tail
-- status  : Open
-- author  : @tc
-- created : 2026-10-09T02:42:30.686207+00:00
-- url     : https://prove2.me/theorems/c927004d-b093-4f9b-8a2c-b6cc07ccb941
-- title:
--   Chen–Dongarra tail bound for $\|G^{\dagger}\|$: $\mathbb P\{\|G^{\dagger}\|>t\}\le\frac{1}{\sqrt{2\pi(k-r+1)}}\bigl(\frac{e\sqrt k}{k-r+1}\bigr)^{k-r+1}t^{-(k-r+1)}$
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with $k\ge r\ge2$, and let $G^{\dagger}=G^{\mathsf T}(GG^{\mathsf T})^{-1}$. For every $t>0$,
--   $$\mathbb P\bigl\{\|G^{\dagger}\|>t\bigr\}\ \le\ \frac{1}{\sqrt{2\pi\,(k-r+1)}}\left(\frac{e\sqrt{k}}{k-r+1}\right)^{k-r+1} t^{-(k-r+1)} .$$
--
--   Since $\|G^{\dagger}\|=1/\sigma_{\min}(G)$, this is a small-ball estimate for the smallest singular value of a Gaussian matrix with polynomial decay of order $k-r+1$. It is the source of both the expected-norm bound $\mathbb E\|G^{\dagger}\|\le e\sqrt k/(k-r)$ and the large-deviation bound (10.6) for the spectral error of the randomized SVD. The exponent $k-r+1$ is sharp.
--
--   **Formalization Note.** The event is $\{t<\|G^{\dagger}\|\}$ with `pinvR` as $G^{\dagger}$; real powers $t^{-(k-r+1)}$ are Mathlib's `rpow`, with $t>0$. The bound is a real number converted to $[0,\infty]$.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), Appendix A.2 p. 64, Proposition A.3 (from Chen–Dongarra, Lemma 4.1): for an $m\times n$ standard Gaussian $G$ with $n\ge m\ge2$ and $t>0$, $\mathbb P\{\|G^\dagger\|>t\}\le\frac{1}{\sqrt{2\pi(n-m+1)}}\bigl(\frac{e\sqrt n}{n-m+1}\bigr)^{n-m+1}t^{-(n-m+1)}$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem pinv_spectral_tail {r k : ℕ} (hr : 2 ≤ r) (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | t < specNorm (pinvR (Matrix.of G))}
      ≤ ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * ((k : ℝ) - r + 1)))
          * (Real.exp 1 * Real.sqrt k / ((k : ℝ) - r + 1)) ^ ((k : ℝ) - r + 1)
          * t ^ (-((k : ℝ) - r + 1))) := by sorry
end GaussianMatrix
