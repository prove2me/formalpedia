-- Prove2me | Theorems.Thm_GaussianMatrix_wishart_lambda_min_tail
-- name    : GaussianMatrix.wishart_lambda_min_tail
-- status  : Open
-- author  : @tc
-- created : 2026-10-09T06:39:46.577281+00:00
-- url     : https://prove2.me/theorems/4939bb72-8cf5-4583-bd8a-a9d70d9d9e87
-- title:
--   Lower tail of the smallest Wishart eigenvalue: $\mathbb P\{\lambda_{\min}(GG^\top)\le t\}\le \frac{1}{\Gamma(k-r+2)}\big(\tfrac{t(k+r)}{2}\big)^{(k-r+1)/2}$
-- statement:
--   Let $1\le r\le k$ be integers and let $G$ be an $r\times k$ random matrix with independent standard normal entries. Let
--   $$\lambda_{\min}(GG^\top)=\min_{x\in\mathbb R^r,\ \|x\|_2=1} x^\top GG^\top x=\sigma_{\min}(G^\top)^2$$
--   be the smallest eigenvalue of the $r\times r$ Wishart matrix $GG^\top$, where $\sigma_{\min}(G^\top)=\inf_{\|x\|_2=1}\|G^\top x\|_2$ is the smallest singular value of the tall $k\times r$ matrix $G^\top$. Then for every $t>0$,
--   $$\mathbb P\big\{\lambda_{\min}(GG^\top)\le t\big\}\;\le\;\frac{1}{\Gamma(k-r+2)}\Big(\frac{t\,(k+r)}{2}\Big)^{(k-r+1)/2}.$$
--
--   The bound comes from Edelman's estimate for the density of $\lambda_{\min}$,
--   $$f_{\lambda_{\min}}(\lambda)\le\frac{2^{(k-r-1)/2}\,\Gamma(\frac{k+1}{2})}{\Gamma(\frac r2)\,\Gamma(k-r+1)}\,\lambda^{(k-r-1)/2}e^{-\lambda/2},\qquad \lambda>0,$$
--   after dropping $e^{-\lambda/2}$, bounding $2^{(k-r+1)/2}\Gamma(\frac{k+1}2)/\Gamma(\frac r2)\le((k+r)/2)^{(k-r+1)/2}$ (via $\Gamma(z+\frac12)\le z^{1/2}\Gamma(z)$ and $(r+i)(k-i)\le((k+r)/2)^2$), and integrating over $(0,t]$.
--
--   This is the key probabilistic input for the tail of $\|G^\dagger\|=\lambda_{\min}(GG^\top)^{-1/2}$ (Chen–Dongarra / Halko–Martinsson–Tropp Prop. A.3) and for the inverse moments $\mathbb E\|(GG^\top)^{-1}\|^p$ (Tropp–Webber Lemma B.3).
--
--   **Formalization Note.** The law of $G$ is `gaussianMatrix r k` on `Fin r → Fin k → ℝ`; $\lambda_{\min}(GG^\top)$ is written `sMin (Matrix.of G)ᵀ ^ 2`. The hypothesis $r\ge1$ is necessary: for $r=0$ the sphere in $\mathbb R^0$ is empty, `sMin` is $0$ and the event is the whole space, while the right-hand side is $<1$ for small $t$. $\Gamma$ is `Real.Gamma` and the exponent is a real power.
-- source:
--   A. Edelman, Eigenvalues and condition numbers of random matrices, SIAM J. Matrix Anal. Appl. 9(4) (1988), Prop. 5.1 (density bound for λ_min of a Wishart matrix); combined as in J. A. Tropp and R. J. Webber, Randomized algorithms for low-rank matrix approximation: design, analysis, and applications, arXiv:2306.12418, Appendix B, proof of Lemma B.3, eqs. (B.5)–(B.7); the statement is eq. (B.7).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem wishart_lambda_min_tail {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ENNReal.ofReal ((1 / Real.Gamma ((k : ℝ) - r + 2))
          * (t * ((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2)) := by sorry

end GaussianMatrix
