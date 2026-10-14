-- Prove2me | Theorems.Thm_OTSensitivity_Consist_eq_85
-- name    : OTSensitivity.Consist.eq_85
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:20.168611+00:00
-- url     : https://prove2.me/theorems/e82e328f-a7fb-43b2-bd88-6ce404321d65
-- title:
--   (85), p. 40 — $a=a_1+a_2$ is uniformly integrable with respect to $(\nu^N)$
-- statement:
--   Let $\mathsf X$, $\mathsf Y$ be Polish, $a_1,a_2:\mathsf Y\to[0,\infty)$ continuous, $a=a_1+a_2$, and let $\pi^N\to\pi$ weakly as probability measures on $\mathsf X\times\mathsf Y$, with second marginals $\nu^N$, $\nu$. Assume (73), $\lim_N\int a\,d\nu^N=\int a\,d\nu<\infty$, and that each $\int a\,d\nu^N$ is finite. Then $a$ is uniformly integrable with respect to $(\nu^N)$:
--   $$\forall\varepsilon>0\ \exists L>0:\quad\int_{A(L)}a\,d\nu^N\le\varepsilon\quad\text{for every }N\in\mathbb N,\qquad A(L)=\{y\in\mathsf Y: a(y)\ge L\}.$$
--
--   Uniform integrability is what allows the optimal transport costs $K(\nu^N,\nu^N_{M,h})$ to be passed to the limit in (86) and the null cells to be controlled.
--
--   **Formalization Note** The paper writes (73) as a limit of expectations, i.e. of real numbers; the finiteness of every $\int a\,d\nu^N$ is made explicit here because (85) is claimed for every $N$, and a single infinite moment would make (85) false for that $N$. Integrals are lower Lebesgue integrals in $[0,+\infty]$; $L$ is a finite positive real.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 21, Case 2, (85), p. 40; (73), p. 38

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- (85), p. 40. Under weak convergence `π^N → π` and (73), with each `∫ a dν^N` finite,
`a = a₁ + a₂` is uniformly integrable with respect to `(ν^N)`: for every `ε > 0` there is
`L > 0` with `∫_{a ≥ L} a dν^N ≤ ε` for every `N`. -/
theorem eq_85 {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (a₁ a₂ : 𝒴 → ℝ≥0) (ha₁ : Continuous a₁) (ha₂ : Continuous a₂)
    (πs : ℕ → ProbabilityMeasure (𝒳 × 𝒴)) (π : ProbabilityMeasure (𝒳 × 𝒴))
    (hπ : Tendsto πs atTop (𝓝 π))
    (h73 : MomentConvergence a₁ a₂ (fun N => (πs N : Measure (𝒳 × 𝒴))) (π : Measure (𝒳 × 𝒴)))
    (hfin : ∀ N, ∫⁻ y, ((a₁ y : ℝ≥0∞) + a₂ y) ∂(πs N : Measure (𝒳 × 𝒴)).snd < ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ L : ℝ≥0, 0 < L ∧ ∀ N,
      ∫⁻ y in {y | L ≤ a₁ y + a₂ y}, ((a₁ y : ℝ≥0∞) + a₂ y) ∂(πs N : Measure (𝒳 × 𝒴)).snd ≤ ε := by sorry

end OTSensitivity.Consist
