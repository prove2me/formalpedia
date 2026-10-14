-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_eq_65
-- name    : OTSensitivity.MaxFun.eq_65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:34.575772+00:00
-- url     : https://prove2.me/theorems/87df75f1-2d51-4369-8e32-42a043116380
-- title:
--   (64)–(65), p. 34 — Jensen: K(ν, ½ν¹ + ½ν²) ≤ ∫ K(ν, ½δ_{y₁} + ½δ_{y₂}) d(ν¹ × ν²)
-- statement:
--   Let $\mathsf Y$ be a Polish space and $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $k(y,y')=0\iff y=y'$. Let $\nu,\nu^1,\nu^2$ be probability measures on $\mathsf Y$ and $\sigma=\nu^1\times\nu^2$. The mixture $\tfrac12\nu^1+\tfrac12\nu^2$ is the $\sigma$-average of the two-point measures $\tfrac12\delta_{y_1}+\tfrac12\delta_{y_2}$ (this is (64)), and
--
--   $$K\big(\nu,\tfrac12\nu^1+\tfrac12\nu^2\big)\le\int_{\mathsf Y\times\mathsf Y}K\big(\nu,\tfrac12\delta_{y_1}+\tfrac12\delta_{y_2}\big)\,d\sigma(y_1,y_2).$$
--
--   This is Jensen's inequality for the convex, lower semicontinuous map $K(\nu,\cdot)$. In the proof of Theorem 5 it is applied to a conditional law split as $\nu^{\mathcal F}_x=\tfrac12\nu^1_x+\tfrac12\nu^2_x$; together with Lemma 4 it shows that a conditional law that is not a Dirac mass makes the inequality of (63) strict.
--
--   **Formalization Note** The page states (65) for $\nu^1,\nu^2$ supported in $S=\operatorname{supp}(\nu)$ and integrates over $S\times S$; the statement here holds for all probability measures $\nu^1,\nu^2$ and integrates over $\mathsf Y\times\mathsf Y$, which contains the page's case. Weights are $1/2$ in $[0,+\infty]$; $K$ is the published `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 5, (64)–(65), p. 34

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- (64)–(65), p. 34: Jensen's inequality for the convex, l.s.c. map `K(ν, ·)` over the
representation `½ν¹ + ½ν² = ∫ (½δ_{y₁} + ½δ_{y₂}) dσ(y₁, y₂)` with `σ = ν¹ × ν²`:
`K(ν, ½ν¹ + ½ν²) ≤ ∫ K(ν, ½δ_{y₁} + ½δ_{y₂}) dσ(y₁, y₂)`. -/
theorem eq_65 {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (ν ν₁ ν₂ : Measure 𝒴) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] :
    RWPI.SqrtLasso.transportCost k ν ((1 / 2 : ℝ≥0∞) • ν₁ + (1 / 2 : ℝ≥0∞) • ν₂) ≤
      ∫⁻ p, RWPI.SqrtLasso.transportCost k ν
          ((1 / 2 : ℝ≥0∞) • Measure.dirac p.1 + (1 / 2 : ℝ≥0∞) • Measure.dirac p.2) ∂(ν₁.prod ν₂) := by sorry

end OTSensitivity.MaxFun
