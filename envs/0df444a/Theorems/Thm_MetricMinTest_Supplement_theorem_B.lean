-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_B
-- name    : MetricMinTest.Supplement.theorem_B
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:38:44.290818+00:00
-- url     : https://prove2.me/theorems/7a777754-dcd1-4b94-bdd7-18e3aa81c29e
-- title:
--   Theorem B, p.2 — gap-decay transition on $d_{b,\alpha,m}$: $C^{\mathrm{na}}\asymp B^{\mathrm{na}}$ in three regimes, $F/H\asymp_b1+\min\{m,|1-2\alpha|^{-1}\}$
-- statement:
--   Fix $b\ge2$, $\alpha>0$ and $m\ge1$, and let $d=d_{b,\alpha,m}$ be the hierarchical metric $d(x,y)=\gamma(1-b^{-\alpha\,\mathrm{lev}(x,y)})$ on $V=\{0,\dots,b-1\}^m$, $k=b^m$ points. Let $\gamma\in(0,1/4]$, $\delta\in(0,1/10]$, $L=\ln(1/\delta)$, and write $H=H_d(\gamma)$, $F=F_d(\gamma)$ for the information and certificate workloads. Then, with constants depending only on $b$ and $\alpha$,
--   $$C^{\mathrm{na}}_d(\gamma,\delta)\asymp B^{\mathrm{na}}_d(\gamma,\delta)\asymp\begin{cases}\gamma^{-2}k^{2\alpha}L,&\alpha<1/2,\\ \gamma^{-2}k+HL,&\alpha=1/2,\\ \gamma^{-2}k\ln(k/\delta),&\alpha>1/2.\end{cases}$$
--   For $\alpha\ne1/2$, moreover $F\asymp H$ and $C^\star_d(\gamma,\delta)\asymp B^\star_d(\gamma,\delta)\asymp HL$. Uniformly in $\alpha>0$, with constants depending only on $b$,
--   $$\frac FH\asymp_b1+\min\{m,|1-2\alpha|^{-1}\},\qquad 1/0=\infty .$$
--
--   The theorem locates the nonadaptive phase transition at the critical exponent $\alpha=1/2$, where every distance scale contributes equally to the information constraints, and shows that the certificate ratio reaches logarithmic size only in a window of width $O(1/\log k)$ around it.
--
--   **Formalization Note** Each $\asymp$ is the chain $c\,X\le C^{\mathrm{na}}\le B^{\mathrm{na}}\le C\,X$ (resp. $c\,HL\le C^\star\le B^\star\le C\,HL$).
--
--   Differences from the source:
--   - encoding: $d=d_{b,\alpha,m}$ on $k=b^m$ points → $m\ge1$; reason: the hierarchy family is defined for $m\ge1$ (§4.1; Theorem 5.1, Proposition 5.2)
--   - encoding: $\delta\le1/10$ → $\delta\in(0,1/10]$; reason: standing $\delta\in(0,1/4]$ (§2)
--   - encoding: $\asymp$ with constants depending only on $b$ and $\alpha$; $\asymp_b$ uniformly in $\alpha$ → explicit constants $c,C>0$ quantified before every variable they must not depend on; reason: the paper's convention for $\asymp$, $O$, $\Theta$, $\Omega$ (§2, p.6)
--   - encoding: $C^{\mathrm{na}}\asymp B^{\mathrm{na}}\asymp X$ and $C^\star\asymp B^\star\asymp HL$ → the chains $cX\le C^{\mathrm{na}}\le B^{\mathrm{na}}\le CX$ and $cHL\le C^\star\le B^\star\le CHL$; reason: $C^{\mathrm{na}}\le B^{\mathrm{na}}$ and $C^\star\le B^\star$ hold by definition (pp.6, 9)
--   - encoding: $|1-2\alpha|^{-1}$ with $1/0=\infty$ → $\min\{m,|1-2\alpha|^{-1}\}$ for $\alpha\ne1/2$ and $m$ at $\alpha=1/2$; reason: same value under the convention $1/0=\infty$
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem B, p.2

import Mathlib
import Definitions.Def_MetricMinTest_geomMetric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Cna
import Definitions.Def_MetricMinTest_Bna
import Definitions.Def_MetricMinTest_Bstar
import Definitions.Def_MetricMinTest_Supplement_Cstar

namespace MetricMinTest.Supplement

/-- **Theorem B (Gap-decay transition).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem B, p.2: "Fix b ≥ 2 and α > 0, let
d = d_{b,α,m} on k = b^m points, and let γ ∈ (0, 1/4] and δ ≤ 1/10. Then
C^na_d(γ, δ) ≍ B^na_d(γ, δ) ≍ γ⁻²k^{2α}L (α < 1/2), γ⁻²k + HL (α = 1/2), γ⁻²k ln(k/δ)
(α > 1/2), with constants depending only on b and α. For α ≠ 1/2, F ≍ H and
C⋆_d(γ, δ) ≍ B⋆_d(γ, δ) ≍ HL. Uniformly in α, the certificate ratio satisfies
F/H ≍_b 1 + min{m, |1 − 2α|⁻¹}."

**Formalization Note.** `d = geomMetric b m α γ` on `Fin m → Fin b` with `m ≥ 1` (the standing
range of the hierarchy family, §4.1 and Theorem 5.1); `L = ln(1/δ)`, `δ ∈ (0, 1/10]`. The
first three `≍` and `F ≍ H` use constants `c, C > 0` chosen after `b, α` and before
`m, γ, δ`; each `≍` chain is `c·X ≤ C^na ≤ B^na ≤ C·X` (resp. for `C⋆ ≤ B⋆`). The ratio clause
uses constants chosen after `b` only, before `α, m, γ`, with `1/0 = ∞` so that at `α = 1/2` the
minimum is `m`. -/
theorem theorem_B :
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
        (α ≠ 1 / 2 →
          c * infoWorkload (geomMetric b m α γ) γ ≤ certWorkload (geomMetric b m α γ) γ ∧
          certWorkload (geomMetric b m α γ) γ ≤ C * infoWorkload (geomMetric b m α γ) γ ∧
          ENNReal.ofReal (c * (infoWorkload (geomMetric b m α γ) γ * Real.log (1 / δ))) ≤
            Cstar (geomMetric b m α γ) γ δ ∧
          Cstar (geomMetric b m α γ) γ δ ≤ Bstar (geomMetric b m α γ) γ δ ∧
          Bstar (geomMetric b m α γ) γ δ ≤
            ENNReal.ofReal (C * (infoWorkload (geomMetric b m α γ) γ * Real.log (1 / δ))))) ∧
    (∀ b : ℕ, 2 ≤ b → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ α : ℝ, 0 < α → ∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        c * (1 + (if α = 1 / 2 then (m : ℝ) else min (m : ℝ) |1 - 2 * α|⁻¹)) ≤
          certWorkload (geomMetric b m α γ) γ / infoWorkload (geomMetric b m α γ) γ ∧
        certWorkload (geomMetric b m α γ) γ / infoWorkload (geomMetric b m α γ) γ ≤
          C * (1 + (if α = 1 / 2 then (m : ℝ) else min (m : ℝ) |1 - 2 * α|⁻¹))) := by sorry

end MetricMinTest.Supplement
