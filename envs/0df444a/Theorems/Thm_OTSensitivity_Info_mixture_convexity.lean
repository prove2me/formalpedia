-- Prove2me | Theorems.Thm_OTSensitivity_Info_mixture_convexity
-- name    : OTSensitivity.Info.mixture_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:03.760309+00:00
-- url     : https://prove2.me/theorems/520f550d-6541-4117-ad5d-437dae677f0b
-- title:
--   Proof of Theorem 8 — Jensen step: K(ν, ∫ηₓ dρ) ≤ ∫ K(ν, ηₓ) dρ
-- statement:
--   Let $\mathsf X,\mathsf Y$ be Polish spaces and $\mathsf k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ a continuous cost vanishing exactly on the diagonal, with optimal-transport cost $K$ as in (1). Let $\nu$ be a probability measure on $\mathsf Y$, $\rho$ a probability measure on $\mathsf X$, and $(\eta_x)_{x\in\mathsf X}$ a measurable family of probability measures on $\mathsf Y$ (a Markov kernel). Then
--   $$K\Big(\nu,\int_{\mathsf X}\eta_x\,d\rho(x)\Big)\ \le\ \int_{\mathsf X}K(\nu,\eta_x)\,d\rho(x).$$
--
--   This is the convexity of $K(\nu,\cdot)$ in its Jensen form for mixtures. In the proof of Theorem 8 it is applied with $\rho=\mu^{\mathcal F}_{x'}$ and $\eta_x=\nu_x$, and in the case $\mathcal F=\sigma(g)$ with $\rho=\mu_u$.
--
--   **Formalization Note** Both sides are in $[0,+\infty]$; the right side is a lower Lebesgue integral. The mixture is `ρ.bind η`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 8, display after (67), p. 35

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTSensitivity.Info

/-- Proof of Theorem 8, p. 35 ("Using the convexity of K(ν, ·) and Jensen inequality"): for a
probability measure `ρ` on `𝓧` and a Markov kernel `η` from `𝓧` to `𝓨`, the transport cost from `ν`
to the mixture `∫ η x dρ(x)` is at most the `ρ`-average of the transport costs from `ν` to `η x`. -/
theorem mixture_convexity {𝓧 𝓨 : Type*}
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν]
    (ρ : Measure 𝓧) [IsProbabilityMeasure ρ] (η : Kernel 𝓧 𝓨) [IsMarkovKernel η] :
    RWPI.SqrtLasso.transportCost k ν (ρ.bind η)
      ≤ ∫⁻ x, RWPI.SqrtLasso.transportCost k ν (η x) ∂ρ := by sorry

end OTSensitivity.Info
