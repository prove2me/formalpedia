-- Prove2me | Theorems.Thm_HighDimStat_MetricEntropy_dudley_entropy_integral_bound
-- name    : HighDimStat.MetricEntropy.dudley_entropy_integral_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:02:55.020976+00:00
-- url     : https://prove2.me/theorems/be8a535f-72c9-4dc8-a8cb-4021fa0ba17c
-- title:
--   Theorem 5.22 -- Dudley's entropy integral bound
-- statement:
--   **Theorem 5.22 (Dudley's entropy integral bound).** Let $\{X_\theta,\theta\in T\}$ be a
--   zero-mean sub-Gaussian process with respect to the induced pseudometric $\rho_X$ from
--   Definition 5.16. Then for any $\delta \in [0,D]$,
--
--   $$
--   \mathbb E\Big[\sup_{\theta,\theta'\in T}(X_\theta-X_{\theta'})\Big] \;\le\;
--   2\,\mathbb E\Big[\sup_{\substack{\gamma,\gamma'\in T\\\rho_X(\gamma,\gamma')\le\delta}}(X_\gamma-X_{\gamma'})\Big]
--   + 32\,J(\delta/4; D).
--   $$
--
--   This is the chapter's title result: a substantial sharpening of the one-step discretization
--   bound (Proposition 5.17) obtained by chaining — decomposing the supremum into a telescoping
--   sum of finite maxima over successively refined covers rather than a single discretization
--   step — due originally to Dudley (1967). It is the classical general-purpose tool for bounding
--   the expected supremum of a sub-Gaussian process (equivalently, via the usual centering
--   argument, a Gaussian or Rademacher complexity) purely in terms of the metric entropy of the
--   index set.
--
--   **Formalization Note** The constant $32$ is kept exactly as the book's own proof establishes
--   it; the book explicitly remarks that it "could be improved with a more careful analysis," so a
--   sharper constant from elsewhere would misstate what this particular proof shows. Restricted,
--   as with every definition this theorem depends on, to a finite index type $T$ (a `Fintype`)
--   rather than the book's general totally bounded metric space.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 140 (PDF p. 160), Theorem 5.22, Eq. (5.46)

import Mathlib
import Definitions.Def_HighDimStat_MetricEntropy_SubGaussianProcess
import Definitions.Def_HighDimStat_MetricEntropy_CoveringNumber
import Definitions.Def_HighDimStat_MetricEntropy_Diameter
import Definitions.Def_HighDimStat_MetricEntropy_EntropyIntegral
import Definitions.Def_HighDimStat_MetricEntropy_IncrementSup
import Definitions.Def_HighDimStat_MetricEntropy_LocalIncrementSup

open MeasureTheory

namespace HighDimStat.MetricEntropy

/-- **Theorem 5.22** (Dudley's entropy integral bound), Wainwright, *High-Dimensional Statistics*
(2019), Eq. (5.46), p. 140. Let `{Xθ, θ ∈ T}` be a zero-mean sub-Gaussian process with respect to
the induced pseudometric `ρX` (Definition 5.16). Then for any `δ ∈ [0, D]`,
`E[sup_{θ,θ'} (Xθ - Xθ')] ≤ 2 E[sup_{ρX(γ,γ')≤δ} (Xγ - Xγ')] + 32 J(δ/4; D)`. -/
theorem dudley_entropy_integral_bound {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess Prob X) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδD : δ ≤ Diameter T) :
    ∫ ω, IncrementSup X ω ∂Prob ≤
      2 * (∫ ω, LocalIncrementSup X δ ω ∂Prob) +
      32 * EntropyIntegral T (δ / 4) (Diameter T) := by sorry

end HighDimStat.MetricEntropy
