-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_C
-- name    : MetricMinTest.Supplement.theorem_C
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:40:05.509656+00:00
-- url     : https://prove2.me/theorems/419c804e-5356-4c6d-b591-fe3bc7f6cc3f
-- title:
--   Theorem C, p.2 — shared screening on every metric: $\tfrac18HL\le C^\star\le H(15L+16\ln\rho+1)$, $B^\star=O(H\min\{L(1+\ln\rho),\ln(k/\delta)\})$
-- statement:
--   Let $d$ be a finite metric or pseudometric on $k$ points, $\gamma,\delta\in(0,1/4]$, $L=\ln(1/\delta)$, $H=H_d(\gamma)$ the information workload and $\rho=k\gamma^{-2}/H$ the screening ratio. Then
--   $$\tfrac18HL\le C^\star_d(\gamma,\delta)\le H(15L+16\ln\rho+1),\qquad B^\star_d(\gamma,\delta)=O\big(H\min\{L(1+\ln\rho),\ln(k/\delta)\}\big).$$
--   Consequently $C^\star_d(\gamma,\delta)=\Theta(HL)$ whenever $\delta\le1/\rho$. In the expected upper bound, $(H,\rho)$ may be replaced by the workload and ratio $(H_{Z,r},\rho_{Z,r})$ of any screening cover: for every $r\in[0,\gamma)$ and every $r$-cover $Z$ (Definition 7.1),
--   $$C^\star_d(\gamma,\delta)\le H_{Z,r}(15L+16\ln\rho_{Z,r}+1).$$
--
--   The theorem shows that on every metric the adaptive expected cost is the information workload times $\ln(1/\delta)$, up to the additive screening term $\ln\rho$.
--
--   **Formalization Note** The $O$ and the $\Theta$ use absolute constants chosen before the metric, $\gamma$ and $\delta$.
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - encoding: $O(\cdot)$ and $\Theta(\cdot)$ with absolute constants → explicit constants $c,C>0$ quantified before every variable they must not depend on; reason: the paper's convention for $\asymp$, $O$, $\Theta$, $\Omega$ (§2, p.6)
--   - encoding: screening cover (Definition 7.1) → an $r$-cover $Z$ with $r\in[0,\gamma)$ and its $H_{Z,r}$, $\rho_{Z,r}$; reason: Definition 7.1
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem C, p.2

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_IsRCover
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_regionRatio
import Definitions.Def_MetricMinTest_Bstar
import Definitions.Def_MetricMinTest_Supplement_Cstar

namespace MetricMinTest.Supplement

/-- **Theorem C (Shared screening on every metric).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem C, p.2: "For every finite
metric or pseudometric and γ, δ ∈ (0, 1/4], (1/8)HL ≤ C⋆_d(γ, δ) ≤ H(15L + 16 ln ρ + 1),
B⋆_d(γ, δ) = O(H min{L(1 + ln ρ), ln(k/δ)}). Consequently C⋆_d(γ, δ) = Θ(HL) whenever δ ≤ 1/ρ. In
the expected upper bound, (H, ρ) may also be replaced by the workload and ratio of any screening
cover (Definition 7.1)."

**Formalization Note.** `d` is a pseudometric (a metric is a special case) on a finite nonempty
index type, `k = |ι|`; `H = infoWorkload d γ`, `ρ = kγ⁻²/H = regionRatio d γ univ 0`,
`L = ln(1/δ)`. The `O` and the `Θ` use absolute constants chosen before the index type, the
metric, `γ` and `δ`. A screening cover is an `r`-cover `Z` (`IsRCover`) with `r ∈ [0, γ)`
(Definition 7.1), with workload `H_{Z,r}` and ratio `ρ_{Z,r}`. -/
theorem theorem_C :
    ∃ C₁ c₂ C₂ : ℝ, 0 < C₁ ∧ 0 < c₂ ∧ 0 < C₂ ∧
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ), IsPseudometric d →
      ∀ γ δ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → δ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        ENNReal.ofReal (infoWorkload d γ * Real.log (1 / δ) / 8) ≤ Cstar d γ δ ∧
        Cstar d γ δ ≤ ENNReal.ofReal (infoWorkload d γ *
          (15 * Real.log (1 / δ) + 16 * Real.log (regionRatio d γ Finset.univ 0) + 1)) ∧
        Bstar d γ δ ≤ ENNReal.ofReal (C₁ * infoWorkload d γ *
          min (Real.log (1 / δ) * (1 + Real.log (regionRatio d γ Finset.univ 0)))
            (Real.log ((Fintype.card ι : ℝ) / δ))) ∧
        (δ ≤ 1 / regionRatio d γ Finset.univ 0 →
          ENNReal.ofReal (c₂ * infoWorkload d γ * Real.log (1 / δ)) ≤ Cstar d γ δ ∧
          Cstar d γ δ ≤ ENNReal.ofReal (C₂ * infoWorkload d γ * Real.log (1 / δ))) ∧
        ∀ (Z : Finset ι) (r : ℝ), 0 ≤ r → r < γ → IsRCover d Z r →
          Cstar d γ δ ≤ ENNReal.ofReal (regionWorkload d γ Z r *
            (15 * Real.log (1 / δ) + 16 * Real.log (regionRatio d γ Z r) + 1)) := by sorry

end MetricMinTest.Supplement
