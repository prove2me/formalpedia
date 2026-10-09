-- Prove2me | Theorems.Thm_HairerLiFBM_SemiDet_lemma_2_2
-- name    : HairerLiFBM.SemiDet.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:05.99534+00:00
-- url     : https://prove2.me/theorems/085a0e31-8f75-4da2-a82e-6cfbbf197640
-- title:
--   Lemma 2.2 — stability of Young equations with a common initial value
-- statement:
--   Let $F:\mathbb R^d\to L(\mathbb R^m,\mathbb R^d)$ be bounded and twice continuously differentiable with bounded derivatives. Let $b$ be $\beta$-Hölder, and let $z$ and $\bar z$ solve $z=Z+\int F(z)\,db$ and $\bar z=\bar Z+\int F(\bar z)\,db$ on $[0,1]$, with $\alpha+\beta>1$, $0<\alpha\le\beta\le1$, and $Z_0=\bar Z_0$. Then
--
--   $$|z-\bar z|_\alpha \le C\exp\left(C|b|_\beta^{1/\beta}+C|Z|_\alpha^{1/\alpha}+C|\bar Z|_\alpha^{1/\alpha}\right)|Z-\bar Z|_\alpha.$$
--
--   The constant depends on $F$, the dimensions, and the two Hölder exponents. This deterministic residual estimate turns a small difference of the two forcing terms into a small difference of solutions.
--
--   **Formalization Note** The displayed source statement omits $Z_0=\bar Z_0$ and says $C$ depends only on $F$. With the paper's homogeneous seminorm, the printed statement is false for unequal constant initial forcings; both uses in the paper have equal initial values. The Young estimate also makes $C$ depend on $\alpha,\beta$.
-- source:
--   Hairer and Li, Averaging dynamics driven by fractional Brownian motion, Ann. Probab. 48(4) (2020), https://doi.org/10.1214/19-AOP1408, pp. 1829–1830, Lemma 2.2 and proof

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model

namespace HairerLiFBM.SemiDet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Lemma 2.2, pp. 1829–1830, with the common-initial-value correction. -/
theorem lemma_2_2 :
    ∀ (m d : ℕ) (α β : ℝ), 0 < m → 0 < d →
      1 / 2 < β → β ≤ 1 → 0 < α → α ≤ β → 1 < α + β →
      ∀ F : E d → (E m →L[ℝ] E d), IsBC2 F →
        ∃ C : ℝ, 0 < C ∧
          ∀ (b : ℝ → E m) (Z Zbar z zbar : ℝ → E d),
            holderSemi β (Set.Icc 0 1) b < ⊤ →
            holderSemi α (Set.Icc 0 1) Z < ⊤ →
            holderSemi α (Set.Icc 0 1) Zbar < ⊤ →
            Z 0 = Zbar 0 →
            holderSemi α (Set.Icc 0 1) z < ⊤ →
            holderSemi α (Set.Icc 0 1) zbar < ⊤ →
            (∀ t ∈ Set.Icc 0 1,
              IsYoungIntegral (fun r => F (z r)) b 0 t (z t - Z t)) →
            (∀ t ∈ Set.Icc 0 1,
              IsYoungIntegral (fun r => F (zbar r)) b 0 t (zbar t - Zbar t)) →
            holderSemi α (Set.Icc 0 1) (fun t => z t - zbar t) ≤
              ENNReal.ofReal
                (C * Real.exp
                  (C * (holderSemi β (Set.Icc 0 1) b).toReal ^ (1 / β) +
                    C * (holderSemi α (Set.Icc 0 1) Z).toReal ^ (1 / α) +
                    C * (holderSemi α (Set.Icc 0 1) Zbar).toReal ^ (1 / α))) *
                holderSemi α (Set.Icc 0 1) (fun t => Z t - Zbar t) := by sorry

end HairerLiFBM.SemiDet
