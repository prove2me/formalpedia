-- Prove2me | Theorems.Thm_OTSensitivity_Consist_cell_convergence
-- name    : OTSensitivity.Consist.cell_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:13.561987+00:00
-- url     : https://prove2.me/theorems/e37986a1-c084-48a8-b9b0-55bd497a06ad
-- title:
--   p. 40 — $\nu^N\to\nu$, $\mu^N(X^M_h)\to\mu(X^M_h)$ and $\nu^N_{M,h}\to\nu_{M,h}$ for cells of positive mass
-- statement:
--   Let $\mathsf X$, $\mathsf Y$ be Polish and let $\pi^N\to\pi$ weakly as probability measures on $\mathsf X\times\mathsf Y$, with marginals $\mu^N,\nu^N$ and $\mu,\nu$. Let $A\subseteq\mathsf X$ be measurable with $\mu(\partial A)=0$, and write $\nu^N_A(B)=\mu^N(A)^{-1}\pi^N(A\times B)$, $\nu_A(B)=\mu(A)^{-1}\pi(A\times B)$. Then
--
--   1. $\nu^N\to\nu$ weakly;
--   2. $\mu^N(A)\to\mu(A)$;
--   3. if $\mu(A)>0$, then $\nu^N_A\to\nu_A$ weakly.
--
--   Applied to the cells $A=X^M_h$ of a partition satisfying (75), this is the first sentence of the proof of (82).
--
--   **Formalization Note** Weak convergence of $\pi^N$ is Mathlib's topology on probability measures; the conclusions are stated by testing against bounded continuous nonnegative functions. For the finitely many $N$ with $\mu^N(A)=0$ the formula for $\nu^N_A$ gives the zero measure, which does not affect the limit.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 21, Case 2, first sentence of p. 40 (also Case 1, p. 39)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- p. 40 (first sentence of the proof of (82)). If `π^N → π` weakly and `A ⊆ 𝒳` is measurable with
`μ(∂A) = 0`, then `ν^N → ν` weakly, `μ^N(A) → μ(A)`, and, when `μ(A) > 0`, the cell laws
`ν^N_A → ν_A` weakly. -/
theorem cell_convergence {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (πs : ℕ → ProbabilityMeasure (𝒳 × 𝒴)) (π : ProbabilityMeasure (𝒳 × 𝒴))
    (hπ : Tendsto πs atTop (𝓝 π))
    (A : Set 𝒳) (hA : MeasurableSet A) (hAπ : (π : Measure (𝒳 × 𝒴)).fst (frontier A) = 0) :
    WeakConv (fun N => (πs N : Measure (𝒳 × 𝒴)).snd) (π : Measure (𝒳 × 𝒴)).snd ∧
      Tendsto (fun N => (πs N : Measure (𝒳 × 𝒴)).fst A) atTop
        (𝓝 ((π : Measure (𝒳 × 𝒴)).fst A)) ∧
      ((π : Measure (𝒳 × 𝒴)).fst A ≠ 0 →
        WeakConv (fun N => cellLaw (πs N : Measure (𝒳 × 𝒴)) A) (cellLaw (π : Measure (𝒳 × 𝒴)) A)) := by sorry

end OTSensitivity.Consist
