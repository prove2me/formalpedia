-- Prove2me | Theorems.Thm_OTSensitivity_Consist_eq_83
-- name    : OTSensitivity.Consist.eq_83
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:20.989083+00:00
-- url     : https://prove2.me/theorems/3fa09916-a59e-4b8e-a3a7-763a3e7db7e0
-- title:
--   (83), p. 39 — $\xi^K(Y,X\mid\mathcal F^M)=\sum_{h\in H(M)}\mu(X^M_h)K(\nu,\nu_{M,h})$
-- statement:
--   Let $\mathsf X$, $\mathsf Y$ be Polish, $k$ a cost satisfying the standing assumption of §3.1, and $\pi$ a probability measure on $\mathsf X\times\mathsf Y$ with marginals $\mu$, $\nu$. Let $\{X_h\}_{h=1}^{n}$ be a finite measurable partition of $\mathsf X$ generating the $\sigma$-algebra $\mathcal F'$, let $H=\{h:\mu(X_h)>0\}$, and for $h\in H$ let $\nu_h(B)=\mu(X_h)^{-1}\pi(X_h\times B)$. Then, for every version of the conditional distribution of $Y$ given $(X,\mathcal F')$,
--   $$\xi^K(Y,X\mid\mathcal F')=\sum_{h\in H}\mu(X_h)\,K(\nu,\nu_h).$$
--   With $\mathcal F'=\mathcal F^M$ this is (83); applied to $\pi^N$ it is the corrected (84).
--
--   The identity turns the sensitivity measure with respect to a partition into a finite sum of optimal transport costs, which is the form in which the partition estimator is computed.
--
--   **Formalization Note** Polish $\mathsf X$, $\mathsf Y$; joint-law encoding ($\Omega=\mathsf X\times\mathsf Y$, coordinate projections); values in $[0,+\infty]$; $K$ is `RWPI.SqrtLasso.transportCost`; every version of the conditional law.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), proof of Theorem 21, Case 2, (83) and the definitions of µ_{M,h}, H(M), ν_{M,h}, p. 39

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- (83), p. 39. For a finite measurable partition `{X_h}` of `𝒳` generating `𝓕'` and a probability
law `π` of `(X, Y)`, `ξ^K(Y, X | 𝓕') = Σ_{h ∈ H} μ(X_h) K(ν, ν_h)` with `H = {h : μ(X_h) > 0}` and
`ν_h(B) = μ(X_h)⁻¹ π(X_h × B)`, for every version of the conditional distribution. -/
theorem eq_83 {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (π : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure π] {n : ℕ} (C : Fin n → Set 𝒳)
    (hC : IsFinitePartition C) (κ : Kernel 𝒳 𝒴)
    (hκ : IsCondDistrib π Prod.fst Prod.snd (cellSigma C) κ) :
    xi k π Prod.fst Prod.snd κ =
      ∑ h ∈ Finset.univ.filter (fun h => π.fst (C h) ≠ 0),
        π.fst (C h) * RWPI.SqrtLasso.transportCost k π.snd (cellLaw π (C h)) := by sorry

end OTSensitivity.Consist
