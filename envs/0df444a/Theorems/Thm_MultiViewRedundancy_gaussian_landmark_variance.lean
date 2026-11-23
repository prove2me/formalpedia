-- Prove2me | Theorems.Thm_MultiViewRedundancy_gaussian_landmark_variance
-- name    : MultiViewRedundancy.gaussian_landmark_variance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:20:02.253784+00:00
-- url     : https://prove2.me/theorems/1d02d8e3-7deb-4271-a8ab-9871c3d3d666
-- title:
--   Proposition 5 (as proved): the landmark variance in the Gaussian model
-- statement:
--   Consider the Gaussian model $H\sim N(0,\sigma^2)$ with $\sigma^2>0$, $X\mid H\sim N(H,1)$, $Z\mid H\sim N(H,1)$ and $X\perp Z\mid H$, and let $Y$ be any label with $|Y|\le1$ almost surely, jointly distributed with $(X,Z)$. With $X$ and $Z_1$ independent with laws $p_X$ and $p_Z$,
--
--   $$\operatorname{var}\big(\mathbb E[Y_1\mid Z_1]\,g^\star(X,Z_1)\big)\le1+\frac{\sigma^4}{1+2\sigma^2}.$$
--
--   Consequently, with the block size $n=\lfloor m/\lceil\log_2(1/\delta)\rceil\rfloor$ used in the landmark statements and $m\ge\lceil\log_2(1/\delta)\rceil$, $\varepsilon_{\mathrm{lm}}\le\frac{2}{n}\Big(1+\frac{\sigma^4}{1+2\sigma^2}\Big)\le\frac{4\lceil\log_2(1/\delta)\rceil}{m}\Big(1+\frac{\sigma^4}{1+2\sigma^2}\Big)$, which is $O\big(\log(1/\delta)/m\big)\big(1+\frac{\sigma^4}{1+2\sigma^2}\big)$ for $\delta\le1/2$.
--
--   **Formalization Note** The paper states $\varepsilon_{\mathrm{lm}}=O(\log(1/\delta)/m)\cdot(1+\sigma^4/(1+2\sigma^2))$ without the constant. Its proof computes $\mathbb E[g^\star(X,\tilde Z)^2]=(1+\sigma^2)^2/(1+2\sigma^2)=1+\sigma^4/(1+2\sigma^2)$, and the statement is that explicit bound on the variance in $\varepsilon_{\mathrm{lm}}$, from which the $O$-bound follows. The law of $(X,Y,Z)$ is any probability measure whose $(X,Z)$-marginal is the Gaussian model.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 3.3, Proposition 5, p. 9; proof in Appendix A.4, pp. 17-18

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem gaussian_landmark_variance (v : ℝ≥0) (hv : 0 < v)
    (ρ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure ρ] (hρ : lawXZ ρ = gaussianModel v)
    (hY : ∀ᵐ t ∂ρ, |t.2.2| ≤ 1) :
    landmarkVar ρ ≤ ENNReal.ofReal (1 + (v : ℝ) ^ 2 / (1 + 2 * v)) := by sorry

end MultiViewRedundancy
