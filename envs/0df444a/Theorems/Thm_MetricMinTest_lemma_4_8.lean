-- Prove2me | Theorems.Thm_MetricMinTest_lemma_4_8
-- name    : MetricMinTest.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:49.697357+00:00
-- url     : https://prove2.me/theorems/3d7dfe1b-8f15-4c12-acf4-ade31198ba68
-- title:
--   Lemma 4.8, p.11 — critical correlations: $K_s\le\gamma^2[6+(1-1/b)(m-s)]$ and $\Psi(2cF/(256k))\le2/9$
-- statement:
--   Fix $b\ge2$, $m\ge1$, $k=b^m$, let $\gamma\in(0,1/4]$ and $d=d_{b,1/2,m}$, with gap profile $g_t=\gamma b^{-t/2}$, correlations $K_s$ and profile $\Psi$. Then
--   $$K_s\le\gamma^2\big[6+(1-1/b)(m-s)\big]\qquad\text{for every level } 0\le s\le m,$$
--   and $\Psi(2cT/k)\le2/9$ for $T=F_d(\gamma)/256$, where $c=(1-\gamma^2)^{-1}$.
--
--   This verifies the hypothesis of Theorem 4.5 at the critical exponent with $T=F/256$.
--
--   Differences from the source:
--   - encoding: "for every $s$" → for every level $0\le s\le m$; reason: $s$ is a level of the hierarchy
--   - encoding: the minimum $F_d(\gamma)$ of (2.1) over indexed balls $B_{j\ell}$ → the real infimum of the feasible costs, with indexed balls encoded by the pairs $(j,i)$ with $d(j,i)<\gamma$; reason: the minimum is attained (p.6) and a repeated distance only duplicates a ball at equal cost, so the value is the same
--   - encoding: $K_s$ defined as $\sum_{y}g_{\mathrm{lev}(x,y)}g_{\mathrm{lev}(x^\prime,y)}$ → $K_s$ defined by the closed form, the second line of (4.1); reason: the two lines are equal by the identity (4.1) on the page
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Lemma 4.8, p.11

import Mathlib
import Definitions.Def_MetricMinTest_geomMetric
import Definitions.Def_MetricMinTest_corrPsi
import Definitions.Def_MetricMinTest_certWorkload

namespace MetricMinTest

/-- **Lemma 4.8 (Critical correlations).** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Lemma 4.8, p.11: "Let
d = d_{b,1/2,m} and γ ∈ (0, 1/4]. Then K_s ≤ γ²[6 + (1 − 1/b)(m − s)] for every s, and
Ψ(2cT/k) ≤ 2/9 for T = F/256."

**Formalization Note.** Standing §4.1 setting `b ≥ 2`, `m ≥ 1`, `k = b^m`; `c = (1 − γ²)⁻¹`
(Theorem 4.5); `K_s` and `Ψ` are those of the profile `g_t = γ b^{−t/2}` of `d_{b,1/2,m}`;
`F = F_d(γ)`. "Every s" ranges over the levels `0 ≤ s ≤ m`. -/
theorem lemma_4_8 (b m : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m) (γ : ℝ)
    (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) :
    (∀ s : ℕ, s ≤ m →
      corrK b m (geomProfile b (1 / 2) γ) s ≤ γ ^ 2 * (6 + (1 - 1 / (b : ℝ)) * ((m : ℝ) - s))) ∧
    corrPsi b m (geomProfile b (1 / 2) γ)
      (2 * (1 - γ ^ 2)⁻¹ * (certWorkload (geomMetric b m (1 / 2) γ) γ / 256) / (b : ℝ) ^ m)
        ≤ 2 / 9 := by sorry

end MetricMinTest
