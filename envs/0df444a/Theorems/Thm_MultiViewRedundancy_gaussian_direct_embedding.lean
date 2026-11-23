-- Prove2me | Theorems.Thm_MultiViewRedundancy_gaussian_direct_embedding
-- name    : MultiViewRedundancy.gaussian_direct_embedding
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:21:40.432394+00:00
-- url     : https://prove2.me/theorems/3e92f5c5-6c36-401f-ac1e-82c4dce1ad3e
-- title:
--   Proposition 9: direct embeddings in the Gaussian model
-- statement:
--   In the Gaussian model $H\sim N(0,\sigma^2)$, $X\mid H\sim N(H,1)$, $Z\mid H\sim N(H,1)$, $X\perp Z\mid H$, with $0<\sigma^2<1/2$, for every integer $m>0$ there exist measurable $\eta,\psi:\mathbb R\to\mathbb R^m$ with
--
--   $$\varepsilon_{\mathrm{direct}}(\eta,\psi)\le\frac1m\cdot\frac{(1+\sigma^2)^2}{\sqrt{1-4\sigma^4}}.$$
--
--   **Formalization Note** The paper's hypothesis that $Y$ takes values in $[-1,1]$ plays no role, since $\varepsilon_{\mathrm{direct}}$ depends only on the law of $(X,Z)$, and it is omitted. $\sigma^2>0$ is the model's standing assumption (Proposition 5 states it), and $m>0$ is the standing assumption of Lemma 7.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 4.2.2, Proposition 9, p. 12; proof in Appendix A.8, p. 21

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem gaussian_direct_embedding (v : ℝ≥0) (hv0 : 0 < v) (hv : (v : ℝ) < 1 / 2)
    (m : ℕ) (hm : 0 < m) :
    ∃ (η ψ : ℝ → Fin m → ℝ), Measurable η ∧ Measurable ψ ∧
      epsDirect (gaussianModel v) η ψ ≤
        ENNReal.ofReal (1 / m * ((1 + (v : ℝ)) ^ 2 / Real.sqrt (1 - 4 * (v : ℝ) ^ 2))) := by sorry

end MultiViewRedundancy
