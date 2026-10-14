-- Prove2me | Theorems.Thm_OTSensitivity_Consist_eq_86
-- name    : OTSensitivity.Consist.eq_86
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:34.684331+00:00
-- url     : https://prove2.me/theorems/83849ea9-90c6-4c79-81ee-b7dc8989d0b7
-- title:
--   (86), p. 40 — $K(\nu^N,\nu^N_{M,h})\to K(\nu,\nu_{M,h})$ for cells of positive mass
-- statement:
--   Assume the conditions of Theorem 21: $\mathsf X$, $\mathsf Y$ Polish; $k$ continuous with $k(y,y')=0\iff y=y'$; $k(y,y')\le a_1(y)+a_2(y')$ with $a_1,a_2\ge0$ continuous; $\pi^N\to\pi$ weakly on $\mathsf X\times\mathsf Y$; and (73). Let $A\subseteq\mathsf X$ be measurable with $\mu(\partial A)=0$ and $\mu(A)>0$, and let $\nu^N_A$, $\nu_A$ be the conditional laws of the second coordinate on the cell $A$ under $\pi^N$ and $\pi$. Then
--   $$\lim_{N\to\infty}K(\nu^N,\nu^N_A)=K(\nu,\nu_A).$$
--   For $A=X^M_h$ with $h\in H(M)$ this is (86).
--
--   This is the stability of the optimal transport cost along the cell laws, the analytic core of the consistency of the partition estimator.
--
--   **Formalization Note** Polish spaces, joint-law encoding, values in $[0,+\infty]$, $K$ is `RWPI.SqrtLasso.transportCost`. For the finitely many $N$ with $\mu^N(A)=0$ the cell law is the zero measure and $K=+\infty$; this does not affect the limit.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 21, Case 2, (86), p. 40

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- (86), p. 40. Under the conditions of Theorem 21, for a measurable `A ⊆ 𝒳` with `μ(∂A) = 0` and
`μ(A) > 0`, `K(ν^N, ν^N_A) → K(ν, ν_A)`. -/
theorem eq_86 {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (a₁ a₂ : 𝒴 → ℝ≥0) (ha : IsSeparateCostBound k a₁ a₂)
    (πs : ℕ → ProbabilityMeasure (𝒳 × 𝒴)) (π : ProbabilityMeasure (𝒳 × 𝒴))
    (hπ : Tendsto πs atTop (𝓝 π))
    (h73 : MomentConvergence a₁ a₂ (fun N => (πs N : Measure (𝒳 × 𝒴))) (π : Measure (𝒳 × 𝒴)))
    (A : Set 𝒳) (hA : MeasurableSet A) (hAπ : (π : Measure (𝒳 × 𝒴)).fst (frontier A) = 0)
    (hpos : (π : Measure (𝒳 × 𝒴)).fst A ≠ 0) :
    Tendsto (fun N => RWPI.SqrtLasso.transportCost k (πs N : Measure (𝒳 × 𝒴)).snd
        (cellLaw (πs N : Measure (𝒳 × 𝒴)) A)) atTop
      (𝓝 (RWPI.SqrtLasso.transportCost k (π : Measure (𝒳 × 𝒴)).snd
        (cellLaw (π : Measure (𝒳 × 𝒴)) A))) := by sorry

end OTSensitivity.Consist
