-- Prove2me | Theorems.Thm_MetricMinTest_theorem_4_5
-- name    : MetricMinTest.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:12:33.2852+00:00
-- url     : https://prove2.me/theorems/56f5d249-3703-4e56-b584-0fcb2c4e0acf
-- title:
--   Theorem 4.5, p.9 — correlation-profile lower bound for nonadaptive testers
-- statement:
--   Fix $b\ge2$, $m\ge1$, $k=b^m$, let $\gamma\in(0,1/4]$, $\delta\in(0,1/5]$, $c=(1-\gamma^2)^{-1}$, and let $g$ be a gap profile with $g_0=\gamma$, defining $d_g$. If $T>0$ satisfies
--   $$\Psi(2cT/k)\le2/9,$$
--   then every $(\gamma,\delta)$-valid nonadaptive tester for $d_g$ satisfies
--   $$\Pr_\xi[N(\xi)\le T]\le\tfrac92\delta,\qquad\mathbb E_\xi N(\xi)\ge\big(1-\tfrac92\delta\big)T.$$
--   In particular $B^{\mathrm{na}}_{d_g}(\gamma,\delta)>T$; for $\delta\le1/10$, $C^{\mathrm{na}}_{d_g}(\gamma,\delta)\ge\tfrac{11}{20}T$; and in addition $C^{\mathrm{na}}_{d_g}(\gamma,\delta)\ge H_{d_g}(\gamma)\ln(1/\delta)/8$.
--
--   The criterion reduces the nonadaptive lower bound on any hierarchy to $m+1$ correlations of its gap profile.
--
--   **Formalization Note** Nonadaptive testers are valid one-round testers.
--
--   Differences from the source:
--   - reading: "for $\delta\le1/10$ the expected nonadaptive cost is $\Omega(T)$" → $C^{\mathrm{na}}\ge\frac{11}{20}T$; reason: the constant $1-\frac9{20}$ that the displayed bound gives at $\delta\le1/10$; it implies the $\Omega(T)$ form
--   - encoding: "in addition to the information lower bound $H\ln(1/\delta)/8$" → $C^{\mathrm{na}}\ge H\ln(1/\delta)/8$; reason: the bound for the expected cost, which implies it for $B^{\mathrm{na}}\ge C^{\mathrm{na}}$
--   - encoding: nonadaptive tester (Definition 4.4) → valid one-round tester in the stack-of-streams model; reason: Lean model; Definition C.6 identifies them
--   - encoding: the minimum $H_d(\gamma)$ of (1.1) → the real infimum of the feasible masses; reason: the feasible set is nonempty and bounded below and the minimum is attained (p.7), so the value is the same
--   - encoding: $K_s$ defined as $\sum_{y}g_{\mathrm{lev}(x,y)}g_{\mathrm{lev}(x^\prime,y)}$ → $K_s$ defined by the closed form, the second line of (4.1); reason: the two lines are equal by the identity (4.1) on the page
--   - encoding: $N(\xi)<\infty$ almost surely → $\mathbb N$-valued counts for every $\xi$, with the acceptance set and the cost measurable inside validity; reason: a tester with $N(\xi)=\infty$ on a null set can be changed there without changing any law or expectation, and the probabilities and expectations on the page presuppose measurability
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 4.5, p.9

import Mathlib
import Definitions.Def_MetricMinTest_IsGapProfile
import Definitions.Def_MetricMinTest_gapMetric
import Definitions.Def_MetricMinTest_corrPsi
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_Cna
import Definitions.Def_MetricMinTest_Bna

namespace MetricMinTest

open MeasureTheory

/-- **Theorem 4.5 (Correlation-profile lower bound).** Chen–Fang, *Minimum-Mean Testing under
Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem 4.5, p.9:
"Let γ ∈ (0, 1/4], δ ∈ (0, 1/5], and c = (1 − γ²)⁻¹. If T > 0 satisfies Ψ(2cT/k) ≤ 2/9, then
every (γ, δ)-valid nonadaptive tester for d_g satisfies Pr_ξ[N(ξ) ≤ T] ≤ (9/2)δ,
E_ξ N(ξ) ≥ (1 − (9/2)δ)T. In particular B^na_{d_g}(γ, δ) > T, and for δ ≤ 1/10 the expected
nonadaptive cost is Ω(T). These bounds hold in addition to the information lower bound
H_{d_g}(γ) ln(1/δ)/8."

**Formalization Note.** Standing §4.1 setting: `b ≥ 2`, `m ≥ 1`, `V = Fin m → Fin b`, `k = b^m`,
`g` a gap profile with `g₀ = γ`. Nonadaptive testers are valid `RoundTester V 1`. "Ω(T)" is stated
with the constant `1 − 9/20 = 11/20` that the displayed bound gives at `δ ≤ 1/10`. The information
lower bound is stated for `C^na` (and so for `B^na ≥ C^na`). -/
theorem theorem_4_5 (b m : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m) (γ δ : ℝ)
    (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 5)) (g : ℕ → ℝ)
    (hg : IsGapProfile m γ g) (T : ℝ) (hT : 0 < T)
    (hΨ : corrPsi b m g (2 * (1 - γ ^ 2)⁻¹ * T / (b : ℝ) ^ m) ≤ 2 / 9) :
    (∀ A : RoundTester (Fin m → Fin b) 1, A.IsValid (gapMetric b m g) γ δ →
      A.μξ {ξ | (A.naCost ξ : ℝ) ≤ T} ≤ ENNReal.ofReal (9 / 2 * δ) ∧
      ENNReal.ofReal ((1 - 9 / 2 * δ) * T) ≤ ∫⁻ ξ, (A.naCost ξ : ENNReal) ∂A.μξ) ∧
    ENNReal.ofReal T < Bna (gapMetric b m g) γ δ ∧
    (δ ≤ 1 / 10 → ENNReal.ofReal (11 / 20 * T) ≤ Cna (gapMetric b m g) γ δ) ∧
    ENNReal.ofReal (infoWorkload (gapMetric b m g) γ * Real.log (1 / δ) / 8) ≤
      Cna (gapMetric b m g) γ δ := by sorry

end MetricMinTest
