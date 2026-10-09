-- Prove2me | Theorems.Thm_HairerLiFBM_SemiDet_lemma_3_3
-- name    : HairerLiFBM.SemiDet.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:08.395976+00:00
-- url     : https://prove2.me/theorems/c5b9c6b6-bb8b-4640-8adc-c1e5b2192891
-- title:
--   Lemma 3.3 — RKHS bound by the negative Hölder norm
-- statement:
--   Let $h$ be continuous on $[0,T]$, with $T>0$, and let $1/2<H<1$ and $0\le\kappa<H-1/2$. Write $R$ for the covariance (3.2) of the future component of fractional Brownian motion, and $\partial_{r,s}^2R$ for its mixed derivative off the diagonal. Then the RKHS quadratic form is absolutely integrable and obeys
--
--   $$\left|\int_0^T\!\int_0^T \partial_{r,s}^2R(r,s)h(r)h(s)\,dr\,ds\right|\le C T^{2H-2\kappa}|h|_{-\kappa}^2.$$
--
--   Here $|h|_{-\kappa}$ is the supremum of $|t-s|^{\kappa-1}|\int_s^t h(r)\,dr|$ for $s,t\in[0,T]$. The constant depends only on $H$ and $\kappa$. This connects time-antiderivative control to the covariance estimate needed in Lemma 3.4.
--
--   **Formalization Note** The covariance $R$ is the one defined by (3.2); its classical mixed derivative agrees with the distributional derivative away from the diagonal. The integral is taken over $(0,T]^2$, which differs from $[0,T]^2$ by a null set. Integrability is explicit so the Bochner integral cannot silently default to zero.
-- source:
--   Hairer and Li, Averaging dynamics driven by fractional Brownian motion, Ann. Probab. 48(4) (2020), https://doi.org/10.1214/19-AOP1408, p. 1832, (3.2)–(3.3); p. 1833, Lemma 3.3 (3.5); pp. 1858–1859, Appendix proof

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model

namespace HairerLiFBM.SemiDet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Lemma 3.3, p. 1833: the RKHS bound for the conditioned fBm covariance. -/
theorem lemma_3_3 :
    ∀ (H κ : ℝ), 1 / 2 < H → H < 1 → 0 ≤ κ → κ < H - 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T →
        ∀ h : ℝ → ℝ, Continuous h →
          Integrable
            (fun q : ℝ × ℝ => d2R H q.1 q.2 * h q.1 * h q.2)
            ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T))) ∧
          ENNReal.ofReal
            |∫ q, d2R H q.1 q.2 * h q.1 * h q.2
              ∂((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioc 0 T)))| ≤
            ENNReal.ofReal (C * T ^ (2 * H - 2 * κ)) * (negHolder κ 0 T h) ^ (2 : ℕ) := by sorry

end HairerLiFBM.SemiDet
