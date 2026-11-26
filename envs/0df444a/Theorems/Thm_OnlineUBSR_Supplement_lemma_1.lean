-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_lemma_1
-- name    : OnlineUBSR.Supplement.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:38:52.065412+00:00
-- url     : https://prove2.me/theorems/1d659108-c902-42a3-952c-c18476553d63
-- title:
--   Lemma 1 (corrected: base assumptions and smoothness) — derivative-estimator bounds
-- statement:
--   Fix $\theta\in[\theta_l,\theta_u]$. Under Assumptions 1–9 and independent double sampling, for every $m\ge1$ the estimator (12) satisfies
--   $$
--   \mathbb E|h'_m(\theta)-h'(\theta)|\le \frac{C_4}{\sqrt m},\qquad
--   \mathbb E|h'_m(\theta)-h'(\theta)|^2\le \frac{C_5}{m},
--   $$
--   where $K_1(m),C_4,C_5$ are the expressions printed in (14).
--
--   Differences from the source:
--   - correction: Assumption 3 bounds $-\ell'(-t)$ → Lean bounds $g_\theta'(t)$; reason: the base theorem and inner-estimator proof use the derivative of $g_\theta$
--   - correction: Assumption 4 starts at $n\ge1$ → Lean includes $n=0$; reason: the inner estimator uses its first-step noise bound
--   - correction: the source leaves inner $t_0$ unrestricted → Lean requires $t_0\in[t_l,t_u]$; reason: the inner estimator applies the interval derivative bound at its initial point
--   - encoding: the paper says Assumptions 7 and 9 make $h$ smooth → Lean explicitly requires differentiability of $h$ and $h'$ on the parameter interval; reason: this prevents `deriv` from returning its default zero at a nonsmooth point
--   - encoding: $A_m/B_m$ is written as an ordinary ratio → Lean uses total real division, equal to zero when $B_m=0$; reason: the printed Assumption 5 is retained and does not rule out a zero empirical denominator
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 1, pp.9–10, equation (14)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR.Supplement

/-- **Lemma 1 (bias and mean-square error of the derivative estimator).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 1, pp.9--10, (14).

**Formalization Note.** `θ` is fixed in the parameter interval, the two batches are independent,
and `K₁,C₄,C₅` are the printed expressions. Assumptions 1--4 use the three corrections of the
published mission. `SmoothObjective` records the paper's statement that Assumptions 7 and 9
make the UBSR objective smooth, preventing `deriv` from taking its default value. Assumption 5
is retained with its printed quantifier at the true shortfall risk; division by a zero empirical
denominator therefore retains Lean's literal value zero. Both expectations are lower Lebesgue
integrals in `ℝ≥0∞`, so a non-integrable estimator has expectation `∞` and cannot satisfy the
bounds vacuously (a Bochner integral would be `0`). -/
theorem lemma_1
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model E) [IsProbabilityMeasure M.ν]
    (S : Bool → ℕ → ℕ → Ω → E)
    (hbank : IsSampleBank μ M S) (h123 : Assumptions1To3 M)
    (h59 : Assumptions5To9 M) (hsmooth : SmoothObjective M)
    (θ : ℝ) (hθ : θ ∈ Set.Icc M.θl M.θu) (hA4 : InnerNoiseBound μ M S 0 θ)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫⁻ ω, ENNReal.ofReal |derivativeEstimator M S 0 m θ ω - deriv (objective M) θ| ∂μ ≤
        ENNReal.ofReal (C4 M θ m / Real.sqrt m)) ∧
      (∫⁻ ω, ENNReal.ofReal (|derivativeEstimator M S 0 m θ ω - deriv (objective M) θ| ^ 2)
          ∂μ ≤ ENNReal.ofReal (C5 M θ m / m)) := by sorry

end OnlineUBSR.Supplement
