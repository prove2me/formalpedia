-- Prove2me | Theorems.Thm_GeoRobustLearn_fact_3_3
-- name    : GeoRobustLearn.fact_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:24.251988+00:00
-- url     : https://prove2.me/theorems/d3f44812-7ef8-4420-add8-eacb7d4d8948
-- title:
--   Fact 3.3 — $\Gamma_\gamma(f^{-1}(1))\le K$ implies $\Pr[f(x)\ne f(x_s)]\le CK\sqrt s$
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $f:\mathbb R^d\to\{0,1\}$ have Borel set $f^{-1}(1)$ with Gaussian surface area $\Gamma_\gamma(f^{-1}(1))\le K$. For $s\in(0,1]$ write $\rho_s=e^{-s}$, $\sigma_s=\sqrt{1-e^{-2s}}$, let $x,z\sim\gamma$ be independent and $x_s=\rho_sx+\sigma_sz$. Then
--
--   $$\Pr[f(x)\ne f(x_s)]\le CK\sqrt s.$$
--
--   This is the noise-stability bound of Klivans, O'Donnell and Servedio (Corollary 14 of [KOS08]); it converts a boundary-volume bound into an approximation bound for Gaussian smoothing.
--
--   Differences from the source:
--   - reading: "a function f" with Γ_γ(f⁻¹(1)) ≤ K → a Boolean, measurable f; reason: Definition 3.1 defines Γ_γ for Borel sets and f(x) ≠ f(x_s) is about a classifier, as in [KOS08]
--   - encoding: "there is a universal constant C" → ∃ C > 0 chosen before d, K, f and s; reason: the meaning of a universal constant
--   - encoding: liminf_{δ→0} γ(A_δ \ A)/δ → liminf as δ → 0⁺ in [0, ∞] with A_δ = Metric.cthickening δ A; reason: δ is a radius; same value
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Fact 3.3, p.14 (PDF p.14)

import Definitions.Def_GeoRobustLearn_BoundaryVolume

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Fact 3.3** (Corollary 14 of [KOS08]), p.14.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

There is a universal constant `C` such that for every `d`, every Boolean `f` on `ℝ^d` with Borel
`f⁻¹(1)` and Gaussian surface area `Γ_γ(f⁻¹(1)) ≤ K`, and every `s ∈ (0, 1]`, with `x, z ∼ γ`
independent and `x_s = ρ_s x + σ_s z`: `Pr[f(x) ≠ f(x_s)] ≤ C K √s`.

**Formalization Note.** `Γ_γ` is `surfaceArea` (Definition 3.1, p.13, stated there for Borel sets,
hence `Measurable f`). `x_s` is the published `probe s x z`, and the pair `(x, z)` has law `γ ⊗ γ`.
`C` is chosen before `d`, `K`, `f` and `s`. -/
theorem fact_3_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (K s : ℝ) (f : Space d → ℝ),
        IsBoolean f → Measurable f → surfaceArea {x | f x = 1} ≤ ENNReal.ofReal K →
        0 < s → s ≤ 1 →
        ((gaussian d).prod (gaussian d)) {p | f p.1 ≠ f (probe s p.1 p.2)} ≤
          ENNReal.ofReal (C * K * Real.sqrt s) := by sorry

end GeoRobustLearn
