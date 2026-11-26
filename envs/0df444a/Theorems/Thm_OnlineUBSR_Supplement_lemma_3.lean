-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_lemma_3
-- name    : OnlineUBSR.Supplement.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:36:44.789937+00:00
-- url     : https://prove2.me/theorems/dde9e726-9e4c-4abc-b436-2bf4957f6a7f
-- title:
--   Lemma 3 (corrected: restored Assumptions 4–6) — second moment of $h'_m$
-- statement:
--   Uniformly for $\theta\in[\theta_l,\theta_u]$ and $m\ge1$, the double-sample derivative estimator satisfies
--   $$
--   \mathbb E[h'_m(\theta)^2]\le \frac{C_5}{m}+\frac{2B_1C_4}{\sqrt m}+B_1^2.
--   $$
--   The constants are the uniform versions required when the estimator is evaluated at random optimization iterates.
--
--   Differences from the source:
--   - correction: the printed lemma lists Assumptions 1–3 and 7–9 only → Lean also requires Assumptions 4–6; reason: the proof invokes Lemma 1 and the constants contain $\sigma$ and $\eta$
--   - correction: Assumption 3 bounds $-\ell'(-t)$ and Assumption 4 starts at one → Lean uses the corrected $g_\theta'$ bound and includes noise index zero; reason: these are required by the inner Theorem 1 estimate
--   - correction: inner $t_0$ is unrestricted → Lean requires $t_0\in[t_l,t_u]$; reason: the inner estimator uses interval derivative control from its first step
--   - reading: $C_4,C_5$ contain the fixed-$\theta$ term $|t_0-h(\theta)|$ → Lean uses its supremum over $[\theta_l,\theta_u]$; reason: Lemma 3 is applied at random iterates and needs uniform constants
--   - encoding: smoothness of $h$ is asserted informally on p.9 → Lean states differentiability of $h$ and $h'$ on the interval; reason: this excludes junk derivatives
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 3, p.29, equation (63)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR.Supplement

/-- **Lemma 3 (second moment of the derivative estimator).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 3, p.29, (63).

**Formalization Note.** The printed hypothesis list omits Assumptions 4--6 although its proof
invokes Lemma 1 and its constants contain `σ,η`; they are restored here. `C₄,C₅` use the
uniform initial-error supremum over the parameter interval, which is the reading required when
the lemma is applied at random iterates. The outer-batch index is arbitrary and changes no
mathematical instance. The expectation is a lower Lebesgue integral in `ℝ≥0∞`, so a
non-integrable estimator has second moment `∞` and cannot satisfy the bound vacuously. -/
theorem lemma_3
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model E) [IsProbabilityMeasure M.ν]
    (S : Bool → ℕ → ℕ → Ω → E) (hbank : IsSampleBank μ M S)
    (h123 : Assumptions1To3 M) (h59 : Assumptions5To9 M)
    (hsmooth : SmoothObjective M)
    (hA4 : ∀ outer θ, θ ∈ Set.Icc M.θl M.θu → InnerNoiseBound μ M S outer θ) :
    ∀ outer θ, θ ∈ Set.Icc M.θl M.θu → ∀ m : ℕ, 1 ≤ m →
      ∫⁻ ω, ENNReal.ofReal ((derivativeEstimator M S outer m θ ω) ^ 2) ∂μ ≤
        ENNReal.ofReal
          (C5Uniform M m / m + 2 * B1 M * C4Uniform M m / Real.sqrt m + B1 M ^ 2) := by sorry

end OnlineUBSR.Supplement
