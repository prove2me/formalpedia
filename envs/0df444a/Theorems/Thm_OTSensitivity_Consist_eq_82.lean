-- Prove2me | Theorems.Thm_OTSensitivity_Consist_eq_82
-- name    : OTSensitivity.Consist.eq_82
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:21.85501+00:00
-- url     : https://prove2.me/theorems/7ee2f6be-46dd-4358-b751-2fec923dc726
-- title:
--   (82), p. 39 — $\lim_N\xi^K(Y^N,X^N\mid\mathcal F^M)=\xi^K(Y,X\mid\mathcal F^M)$
-- statement:
--   Assume the conditions of Theorem 21: $\mathsf X$, $\mathsf Y$ Polish; $k$ continuous with $k(y,y')=0\iff y=y'$; $k(y,y')\le a_1(y)+a_2(y')$ with $a_1,a_2\ge0$ continuous; $\pi^N\to\pi$ weakly on $\mathsf X\times\mathsf Y$; and (73). Let $\{X_h\}_{h=1}^n$ be a finite measurable partition of $\mathsf X$ whose cells have $\mu$-null boundaries, $\mu(\partial X_h)=0$, and let $\mathcal F'$ be the $\sigma$-algebra it generates. Then, for every choice of versions of the conditional distributions,
--   $$\lim_{N\to\infty}\xi^K(Y^N,X^N\mid\mathcal F')=\xi^K(Y,X\mid\mathcal F').$$
--   With $\mathcal F'=\mathcal F^M$ this is (82): for a fixed partition the estimator $\xi^K_{M,N}$ is consistent.
--
--   **Formalization Note** Polish spaces (the paper's supports are such spaces); joint-law encoding $\Omega=\mathsf X\times\mathsf Y$ with coordinate projections; values in $[0,+\infty]$; $K$ is `RWPI.SqrtLasso.transportCost`; every version of the conditional laws. The separate-cost bound and (73) are assumed unconditionally (for bounded $k$ they hold with constant $a_1=a_2$).
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 21, Case 2, (82), p. 39

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- (82), p. 39. Under the conditions of Theorem 21, for a finite measurable partition `{X_h}` of
`𝒳` whose cells have `μ`-null boundaries and its σ-algebra `𝓕'`,
`lim_N ξ^K(Y^N, X^N | 𝓕') = ξ^K(Y, X | 𝓕')`, for every choice of versions. -/
theorem eq_82 {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (a₁ a₂ : 𝒴 → ℝ≥0) (ha : IsSeparateCostBound k a₁ a₂)
    (πs : ℕ → ProbabilityMeasure (𝒳 × 𝒴)) (π : ProbabilityMeasure (𝒳 × 𝒴))
    (hπ : Tendsto πs atTop (𝓝 π))
    (h73 : MomentConvergence a₁ a₂ (fun N => (πs N : Measure (𝒳 × 𝒴))) (π : Measure (𝒳 × 𝒴)))
    {n : ℕ} (C : Fin n → Set 𝒳) (hC : IsFinitePartition C)
    (hCπ : ∀ h, (π : Measure (𝒳 × 𝒴)).fst (frontier (C h)) = 0)
    (κs : ℕ → Kernel 𝒳 𝒴)
    (hκs : ∀ N, IsCondDistrib (πs N : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd (cellSigma C) (κs N))
    (κ : Kernel 𝒳 𝒴) (hκ : IsCondDistrib (π : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd (cellSigma C) κ) :
    Tendsto (fun N => xi k (πs N : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd (κs N)) atTop
      (𝓝 (xi k (π : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd κ)) := by sorry

end OTSensitivity.Consist
