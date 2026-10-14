-- Prove2me | Theorems.Thm_OTSensitivity_Consist_null_cell_limit
-- name    : OTSensitivity.Consist.null_cell_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:25.29684+00:00
-- url     : https://prove2.me/theorems/86643a7c-6044-4e24-b741-df393ad7d6ce
-- title:
--   p. 40 — on a null cell, $\mu^N_{M,h}K(\nu^N,\nu^N_{M,h})\to0$
-- statement:
--   Assume the conditions of Theorem 21 (Polish $\mathsf X$, $\mathsf Y$; standing cost assumption; separate-cost bound $k\le a_1\oplus a_2$; $\pi^N\to\pi$ weakly; (73)). Let $A\subseteq\mathsf X$ be measurable with $\mu(\partial A)=0$ and $\mu(A)=0$. Then
--   $$\lim_{N\to\infty}\mu^N(A)\,K(\nu^N,\nu^N_A)=0.$$
--   For $A=X^M_h$ with $\mu_{M,h}=0$ this is the null-cell step of the proof of (82).
--
--   It shows that cells which are negligible in the limit contribute nothing to the limit of the partition estimator, even though their empirical mass may be positive for every $N$.
--
--   **Formalization Note** Values in $[0,+\infty]$ with $0\cdot\infty=0$: when $\mu^N(A)=0$ the cell law is the zero measure, $K=+\infty$ and the product is $0$, which is the paper's convention that such cells do not appear in the sum (84). Joint-law encoding; $K$ is `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 21, Case 2, case µ_{M,h} = 0, p. 40

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- p. 40 (case `μ_{M,h} = 0` of the proof of (82)). Under the conditions of Theorem 21, for a
measurable `A ⊆ 𝒳` with `μ(∂A) = 0` and `μ(A) = 0`, `μ^N(A) · K(ν^N, ν^N_A) → 0`. -/
theorem null_cell_limit {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (a₁ a₂ : 𝒴 → ℝ≥0) (ha : IsSeparateCostBound k a₁ a₂)
    (πs : ℕ → ProbabilityMeasure (𝒳 × 𝒴)) (π : ProbabilityMeasure (𝒳 × 𝒴))
    (hπ : Tendsto πs atTop (𝓝 π))
    (h73 : MomentConvergence a₁ a₂ (fun N => (πs N : Measure (𝒳 × 𝒴))) (π : Measure (𝒳 × 𝒴)))
    (A : Set 𝒳) (hA : MeasurableSet A) (hAπ : (π : Measure (𝒳 × 𝒴)).fst (frontier A) = 0)
    (hzero : (π : Measure (𝒳 × 𝒴)).fst A = 0) :
    Tendsto (fun N => (πs N : Measure (𝒳 × 𝒴)).fst A *
        RWPI.SqrtLasso.transportCost k (πs N : Measure (𝒳 × 𝒴)).snd
          (cellLaw (πs N : Measure (𝒳 × 𝒴)) A)) atTop (𝓝 0) := by sorry

end OTSensitivity.Consist
