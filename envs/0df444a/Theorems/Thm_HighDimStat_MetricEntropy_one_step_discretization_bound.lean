-- Prove2me | Theorems.Thm_HighDimStat_MetricEntropy_one_step_discretization_bound
-- name    : HighDimStat.MetricEntropy.one_step_discretization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:01:39.876985+00:00
-- url     : https://prove2.me/theorems/c7c5bc88-20ce-4e1f-b0c6-92d462ebe082
-- title:
--   Proposition 5.17 -- one-step discretization bound
-- statement:
--   **Proposition 5.17 (One-step discretization bound).** Let $\{X_\theta,\theta\in T\}$ be a
--   zero-mean sub-Gaussian process with respect to the metric $\rho_X$. Then for any
--   $\delta \in [0,D]$ such that $N_X(\delta;T)\ge 10$,
--
--   $$
--   \mathbb E\Big[\sup_{\theta,\theta'\in T}(X_\theta - X_{\theta'})\Big] \;\le\;
--   2\,\mathbb E\Big[\sup_{\substack{\gamma,\gamma'\in T\\ \rho_X(\gamma,\gamma')\le\delta}}(X_\gamma-X_{\gamma'})\Big]
--   + 4\sqrt{D^2 \log N_X(\delta;T)}.
--   $$
--
--   This is the chapter's basic discretization bound: replace the supremum over $T$ by a finite
--   maximum over a $\delta$-cover, controlled by a union bound over sub-Gaussian tails, plus the
--   approximation error of the cover itself. Theorem 5.22's chaining argument sharpens exactly
--   this bound (Eq. (5.34) is common to both proofs) by iterating it over a geometric sequence of
--   scales rather than applying it once.
--
--   **Formalization Note** The hypothesis $N_X(\delta;T)\ge 10$ is kept exactly as the book states
--   it (not weakened or dropped): it is what licenses the union-bound step over the $N$-element
--   cover in the book's own proof.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 135 (PDF p. 155), Proposition 5.17, Eq. (5.33)

import Mathlib
import Definitions.Def_HighDimStat_MetricEntropy_SubGaussianProcess
import Definitions.Def_HighDimStat_MetricEntropy_CoveringNumber
import Definitions.Def_HighDimStat_MetricEntropy_Diameter
import Definitions.Def_HighDimStat_MetricEntropy_IncrementSup
import Definitions.Def_HighDimStat_MetricEntropy_LocalIncrementSup

open MeasureTheory

namespace HighDimStat.MetricEntropy

/-- **Proposition 5.17** (One-step discretization bound), Wainwright, *High-Dimensional
Statistics* (2019), Eq. (5.33), p. 135. Let `{Xθ, θ ∈ T}` be a zero-mean sub-Gaussian process with
respect to `ρX`. Then for any `δ ∈ [0, D]` with `N(δ; T) ≥ 10`,
`E[sup_{θ,θ'} (Xθ - Xθ')] ≤ 2 E[sup_{ρX(γ,γ')≤δ} (Xγ - Xγ')] + 4√(D² log N(δ; T))`. -/
theorem one_step_discretization_bound {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess Prob X) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδD : δ ≤ Diameter T) (hN : 10 ≤ CoveringNumber T δ) :
    ∫ ω, IncrementSup X ω ∂Prob ≤
      2 * (∫ ω, LocalIncrementSup X δ ω ∂Prob) +
      4 * Real.sqrt (Diameter T ^ 2 * Real.log (CoveringNumber T δ)) := by sorry

end HighDimStat.MetricEntropy
