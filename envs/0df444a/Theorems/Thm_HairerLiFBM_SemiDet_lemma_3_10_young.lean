-- Prove2me | Theorems.Thm_HairerLiFBM_SemiDet_lemma_3_10_young
-- name    : HairerLiFBM.SemiDet.lemma_3_10_young
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:29.538549+00:00
-- url     : https://prove2.me/theorems/7bbc31a8-f0da-468e-aa35-0b7135135521
-- title:
--   Lemmas 3.10 and 3.12 — Young case of integral bound (3.18)
-- statement:
--   Let $B$ be an $m$-dimensional fractional Brownian motion with $1/2<H<1$. Let $x$ be adapted to the increment filtration, with finite process Hölder seminorm $\|x\|_{\alpha,p}$, where $p\ge2$ and $\alpha>1/2$. Let the deterministic coefficient $f$ satisfy the negative Hölder bounds (3.12) with constant $K$, for $0\le\kappa,\gamma\le1$, and assume $H-\kappa>1/2$ and $\bar\eta=H-\kappa+\gamma\alpha>1$. If $f$ is also uniformly $\delta$-Hölder in time, with $\delta+H>1$, its pathwise Young integral obeys
--
--   $$\left\|\int_s^t f(r,x_r)\,dB_r\right\|_{L^p}\le CK\left((t-s)^{H-\kappa}+\|x\|_{\alpha,p}^{\gamma}(t-s)^{H-\kappa+\gamma\alpha}\right),\qquad 0\le s\le t\le T.$$
--
--   The constant depends on the fixed dimensions, exponents, and time horizon, not on the driver, coefficient, process, or times. The bound is the estimate used twice in the proof of Theorem 3.13.
--
--   **Formalization Note** This combines (3.18) of Lemma 3.10 with Lemma 3.12, which identifies the sewing integral with the Young integral under time regularity. The filtration is the increment filtration. The second conditional-expectation estimate (3.19) is outside this item.
-- source:
--   Hairer and Li, Averaging dynamics driven by fractional Brownian motion, Ann. Probab. 48(4) (2020), https://doi.org/10.1214/19-AOP1408, pp. 1836–1837, Lemma 3.10 (3.18) and Lemma 3.12

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model

namespace HairerLiFBM.SemiDet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The Young-integral case of (3.18), by Lemmas 3.10 and 3.12, pp. 1836–1837. -/
theorem lemma_3_10_young :
    ∀ (m d : ℕ) (H p α κ γ T : ℝ),
      0 < m → 0 < d → 1 / 2 < H → H < 1 → 2 ≤ p → 1 / 2 < α →
      0 ≤ κ → κ ≤ 1 → 0 ≤ γ → γ ≤ 1 →
      1 / 2 < H - κ → 1 < H - κ + γ * α → 0 < T →
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ → Ω → E m), IsFBM m H B P → HasHolderPaths m H B P →
          ∀ (x : ℝ → Ω → E d),
            (∀ t, Measurable[incrSigma B t] (x t)) →
            (∀ t, MemLp (x t) (ENNReal.ofReal p) P) →
            procHolder α (ENNReal.ofReal p) T x P < ⊤ →
            ∀ (f : ℝ → E d → (E m →L[ℝ] E d)) (K δ : ℝ),
              NegHolderBound κ γ T K f → 1 < δ + H →
              (∃ M : ℝ, ∀ y s t, 0 ≤ s → 0 ≤ t → |t - s| ≤ 1 →
                ‖f t y - f s y‖ ≤ M * |t - s| ^ δ) →
              ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
                ∀ I : Ω → E d,
                  (∀ᵐ ω ∂P,
                    IsYoungIntegral (fun r => f r (x r ω)) (fun r => B r ω) s t (I ω)) →
                  eLpNorm I (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal (C * K) *
                      (ENNReal.ofReal ((t - s) ^ (H - κ)) +
                        procHolder α (ENNReal.ofReal p) T x P ^ γ *
                          ENNReal.ofReal ((t - s) ^ (H - κ + γ * α))) := by sorry

end HairerLiFBM.SemiDet
