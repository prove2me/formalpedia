-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_5_1
-- name    : MetricMinTest.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:42:44.386199+00:00
-- url     : https://prove2.me/theorems/5464cb71-01dd-457e-8267-531f2831b0e2
-- title:
--   Theorem 5.1, p.13 — nonadaptive phase transition on $d_{b,\alpha,m}$: three regimes, exact $H$ and $F$, $C^\star\asymp B^\star\asymp HL$ for $\alpha\ne1/2$
-- statement:
--   Fix $b\ge2$ and $\alpha>0$, let $k=b^m$ with $m\ge1$, $\gamma\in(0,1/4]$ and $\delta\in(0,1/10]$. On $d=d_{b,\alpha,m}$,
--   $$C^{\mathrm{na}}_d(\gamma,\delta)\asymp B^{\mathrm{na}}_d(\gamma,\delta)\asymp\begin{cases}\gamma^{-2}k^{2\alpha}\ln(1/\delta),&0<\alpha<1/2,\\ \gamma^{-2}k+H_d(\gamma)\ln(1/\delta),&\alpha=1/2,\\ \gamma^{-2}k\ln(k/\delta),&\alpha>1/2,\end{cases}$$
--   where
--   $$H_d(\gamma)=\frac{k}{\gamma^2\big[1+(1-1/b)\sum_{t=1}^mb^{(1-2\alpha)t}\big]},\qquad F_d(\gamma)=\begin{cases}\gamma^{-2}k^{2\alpha},&\alpha<1/2,\\ \gamma^{-2}k,&\alpha\ge1/2.\end{cases}$$
--   All comparison constants may depend on $b$ and $\alpha$, but not on $m$, $\gamma$ or $\delta$. For $\alpha\ne1/2$, unrestricted adaptive testing satisfies $C^\star_d(\gamma,\delta)\asymp B^\star_d(\gamma,\delta)\asymp H_d(\gamma)\ln(1/\delta)$. Consequently, at constant confidence, the one-round versus unrestricted-adaptive gap is constant for $\alpha<1/2$ and $\Theta(\ln k)$ for $\alpha>1/2$.
--
--   This is the formal version of Theorem B's three regimes, with exact workload formulas for the geometric profiles.
--
--   **Formalization Note** The "Consequently" clause is stated at each fixed $\delta\in(0,1/10]$, with constants allowed to depend on $b,\alpha,\delta$: $c\,C^\star\le C^{\mathrm{na}}\le C\,C^\star$ and $c\,B^\star\le B^{\mathrm{na}}\le C\,B^\star$ for $\alpha<1/2$, and the same with the factor $\ln k$ for $\alpha>1/2$.
--
--   Differences from the source:
--   - encoding: $\asymp$ with constants depending on $b$ and $\alpha$ only → explicit constants $c,C>0$ quantified before every variable they must not depend on; reason: the paper's convention for $\asymp$, $O$, $\Theta$, $\Omega$ (§2, p.6)
--   - encoding: $C^{\mathrm{na}}\asymp B^{\mathrm{na}}\asymp X$ and $C^\star\asymp B^\star\asymp H\ln(1/\delta)$ → the chains $cX\le C^{\mathrm{na}}\le B^{\mathrm{na}}\le CX$ and $cHL\le C^\star\le B^\star\le CHL$; reason: $C^{\mathrm{na}}\le B^{\mathrm{na}}$ and $C^\star\le B^\star$ hold by definition (pp.6, 9)
--   - reading: at constant confidence, the one-round versus unrestricted-adaptive gap is constant ($\alpha<1/2$) and $\Theta(\ln k)$ ($\alpha>1/2$) → at every fixed $\delta\in(0,1/10]$, constants $c,C>0$ (depending on $b,\alpha,\delta$) with $c\,C^\star\le C^{\mathrm{na}}\le C\,C^\star$ and $c\,B^\star\le B^{\mathrm{na}}\le C\,B^\star$, with the extra factor $\ln k$ when $\alpha>1/2$; reason: "gap" is read for both the expected-cost and the budget measures (the stronger reading); "constant confidence" is a fixed $\delta$
--   - encoding: $k^{2\alpha}$, $b^{(1-2\alpha)t}$ → real powers ($\mathrm{rpow}$) of $b^m$ and $b$; reason: Lean convention; same values
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 5.1, p.13

import Mathlib
import Definitions.Def_MetricMinTest_geomMetric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Cna
import Definitions.Def_MetricMinTest_Bna
import Definitions.Def_MetricMinTest_Bstar
import Definitions.Def_MetricMinTest_Supplement_Cstar

namespace MetricMinTest.Supplement

/-- **Theorem 5.1 (Nonadaptive phase transition).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 5.1, p.13: "Fix b ≥ 2 and
α > 0, let k = b^m with m ≥ 1, and let γ ∈ (0, 1/4] and δ ∈ (0, 1/10]. On d = d_{b,α,m},
C^na_d(γ, δ) ≍ B^na_d(γ, δ) ≍ γ⁻²k^{2α} ln(1/δ) (0 < α < 1/2), γ⁻²k + H_d(γ) ln(1/δ) (α = 1/2),
γ⁻²k ln(k/δ) (α > 1/2). Here H_d(γ) = k / (γ²[1 + (1 − 1/b) ∑_{t=1}^m b^{(1−2α)t}]),
F_d(γ) = γ⁻²k^{2α} (α < 1/2), γ⁻²k (α ≥ 1/2). All comparison constants may depend on b and α,
but not on m, γ, or δ. For α ≠ 1/2, unrestricted adaptive testing satisfies
C⋆_d(γ, δ) ≍ B⋆_d(γ, δ) ≍ H_d(γ) ln(1/δ). Consequently, at constant confidence, the one-round
versus unrestricted-adaptive gap is constant for α < 1/2 and Θ(ln k) for α > 1/2."

**Formalization Note.** `d = geomMetric b m α γ` on `Fin m → Fin b` (`k = b^m`). Each `≍` is
written as the chain `c·X ≤ C^na ≤ B^na ≤ C·X` (resp. `c·X ≤ C⋆ ≤ B⋆ ≤ C·X`) with `c, C > 0`
chosen after `b, α` and before `m, γ, δ`. The "Consequently" clause is stated at each fixed
`δ ∈ (0, 1/10]` with constants depending on `b, α, δ`: for `α < 1/2`,
`c·C⋆ ≤ C^na ≤ C·C⋆` and `c·B⋆ ≤ B^na ≤ C·B⋆`; for `α > 1/2`, the same with the factor
`ln k`. Powers with real exponents are `Real.rpow`. -/
theorem theorem_5_1 :
    (∀ b : ℕ, 2 ≤ b → ∀ α : ℝ, 0 < α → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ m : ℕ, 1 ≤ m → ∀ γ δ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → δ ∈ Set.Ioc (0 : ℝ) (1 / 10) →
        (α < 1 / 2 →
          ENNReal.ofReal (c * ((γ ^ 2)⁻¹ * ((b : ℝ) ^ m) ^ (2 * α) * Real.log (1 / δ))) ≤
            Cna (geomMetric b m α γ) γ δ ∧
          Cna (geomMetric b m α γ) γ δ ≤ Bna (geomMetric b m α γ) γ δ ∧
          Bna (geomMetric b m α γ) γ δ ≤
            ENNReal.ofReal (C * ((γ ^ 2)⁻¹ * ((b : ℝ) ^ m) ^ (2 * α) * Real.log (1 / δ)))) ∧
        (α = 1 / 2 →
          ENNReal.ofReal (c * ((γ ^ 2)⁻¹ * (b : ℝ) ^ m +
              infoWorkload (geomMetric b m α γ) γ * Real.log (1 / δ))) ≤
            Cna (geomMetric b m α γ) γ δ ∧
          Cna (geomMetric b m α γ) γ δ ≤ Bna (geomMetric b m α γ) γ δ ∧
          Bna (geomMetric b m α γ) γ δ ≤
            ENNReal.ofReal (C * ((γ ^ 2)⁻¹ * (b : ℝ) ^ m +
              infoWorkload (geomMetric b m α γ) γ * Real.log (1 / δ)))) ∧
        (1 / 2 < α →
          ENNReal.ofReal (c * ((γ ^ 2)⁻¹ * (b : ℝ) ^ m * Real.log ((b : ℝ) ^ m / δ))) ≤
            Cna (geomMetric b m α γ) γ δ ∧
          Cna (geomMetric b m α γ) γ δ ≤ Bna (geomMetric b m α γ) γ δ ∧
          Bna (geomMetric b m α γ) γ δ ≤
            ENNReal.ofReal (C * ((γ ^ 2)⁻¹ * (b : ℝ) ^ m * Real.log ((b : ℝ) ^ m / δ)))) ∧
        infoWorkload (geomMetric b m α γ) γ = (b : ℝ) ^ m /
          (γ ^ 2 * (1 + (1 - 1 / (b : ℝ)) *
            ∑ t ∈ Finset.Icc 1 m, (b : ℝ) ^ ((1 - 2 * α) * (t : ℝ)))) ∧
        certWorkload (geomMetric b m α γ) γ =
          (if α < 1 / 2 then (γ ^ 2)⁻¹ * ((b : ℝ) ^ m) ^ (2 * α) else (γ ^ 2)⁻¹ * (b : ℝ) ^ m) ∧
        (α ≠ 1 / 2 →
          ENNReal.ofReal (c * (infoWorkload (geomMetric b m α γ) γ * Real.log (1 / δ))) ≤
            Cstar (geomMetric b m α γ) γ δ ∧
          Cstar (geomMetric b m α γ) γ δ ≤ Bstar (geomMetric b m α γ) γ δ ∧
          Bstar (geomMetric b m α γ) γ δ ≤
            ENNReal.ofReal (C * (infoWorkload (geomMetric b m α γ) γ * Real.log (1 / δ))))) ∧
    (∀ b : ℕ, 2 ≤ b → ∀ α : ℝ, 0 < α → ∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) (1 / 10) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        (α < 1 / 2 →
          ENNReal.ofReal c * Cstar (geomMetric b m α γ) γ δ ≤ Cna (geomMetric b m α γ) γ δ ∧
          Cna (geomMetric b m α γ) γ δ ≤ ENNReal.ofReal C * Cstar (geomMetric b m α γ) γ δ ∧
          ENNReal.ofReal c * Bstar (geomMetric b m α γ) γ δ ≤ Bna (geomMetric b m α γ) γ δ ∧
          Bna (geomMetric b m α γ) γ δ ≤ ENNReal.ofReal C * Bstar (geomMetric b m α γ) γ δ) ∧
        (1 / 2 < α →
          ENNReal.ofReal (c * Real.log ((b : ℝ) ^ m)) * Cstar (geomMetric b m α γ) γ δ ≤
            Cna (geomMetric b m α γ) γ δ ∧
          Cna (geomMetric b m α γ) γ δ ≤
            ENNReal.ofReal (C * Real.log ((b : ℝ) ^ m)) * Cstar (geomMetric b m α γ) γ δ ∧
          ENNReal.ofReal (c * Real.log ((b : ℝ) ^ m)) * Bstar (geomMetric b m α γ) γ δ ≤
            Bna (geomMetric b m α γ) γ δ ∧
          Bna (geomMetric b m α γ) γ δ ≤
            ENNReal.ofReal (C * Real.log ((b : ℝ) ^ m)) * Bstar (geomMetric b m α γ) γ δ)) := by sorry

end MetricMinTest.Supplement
