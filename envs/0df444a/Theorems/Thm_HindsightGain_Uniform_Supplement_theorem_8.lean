-- Prove2me | Theorems.Thm_HindsightGain_Uniform_Supplement_theorem_8
-- name    : HindsightGain.Uniform.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:20.743605+00:00
-- url     : https://prove2.me/theorems/a8cfe02d-a684-48a6-b940-b7b446ba60b6
-- title:
--   Theorem 8 — Refined bound with incident coefficient energies
-- statement:
--   In the model of Section 1.1, let $\zeta_1,\dots,\zeta_n$ be independent nonnegative random variables with finite second moments. Put $b_i^2=\sum_{e\ni i}\|A_e\|_F^2$, the sum of squared coefficients of the interactions involving variable $i$, $M=\sum_i\mathbb E\zeta_i^2$ and $\bar M=\sum_i(\mathbb E\zeta_i)^2$. Then $\mathrm{Val}_A(\zeta)$ is integrable and
--   $$0\le\mathrm{Gap}_A(\zeta)\le\sqrt{\frac5r}\Big(\sum_i\mathrm{Var}(\zeta_i)\,b_i^2\Big)^{1/2}\sum_{k=0}^{r-1}M^{k/2}\bar M^{(r-1-k)/2}.\tag{21}$$
--
--   Theorem 1 follows from it by $\bar M\le M$ and $\sum_i\mathrm{Var}(\zeta_i)b_i^2\le r\sigma_{\max}^2\|A\|_F^2$.
--
--   **Formalization Note** Powers are real powers with $x^0=1$, including at $x=0$.
--
--   Differences from the source:
--   - encoding: independent nonnegative random variables with finite second moments → an iIndepFun family on an arbitrary probability space, almost surely nonnegative, in L²; reason: random variables are identified up to null sets; L² is the finite-second-moment condition
--   - encoding: the expectation E Val_A(ζ), shown finite on p.13 → integrability of Val_A(ζ) asserted as a conjunct of the conclusion; reason: the Bochner integral is 0 for a non-integrable function, so finiteness is stated and proved rather than assumed
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Theorem 8, p.17 (eq. (21)); integrability p.13

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_weights

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HindsightGain.Uniform.Supplement

open HindsightGain.Uniform

/-- Theorem 8, p.17, equation (21), with `b_i² = Σ_{e∋i} ‖A_e‖_F²`, `M = Σ E ζ_i²`,
`M̄ = Σ (E ζ_i)²` and real powers (`x^0 = 1`). Integrability of the weighted optimum is part of
the conclusion. -/
theorem theorem_8 {Ω : Type} [MeasurableSpace Ω] {n D r : ℕ}
    (M : Model n D r) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Fin n → Ω → ℝ) (hindep : iIndepFun ζ μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ ζ i ω) (hsecond : ∀ i, MemLp (ζ i) 2 μ) :
    Integrable (fun ω => val M (fun i => ζ i ω)) μ ∧
      0 ≤ gap M μ ζ ∧
      gap M μ ζ ≤ Real.sqrt (5 / (r : ℝ)) *
        Real.sqrt (∑ i, variance (ζ i) μ * incidentSq M i) *
        ∑ k ∈ Finset.range r, secondMomentSum μ ζ ^ ((k : ℝ) / 2) *
          meanSqSum μ ζ ^ (((r : ℝ) - 1 - (k : ℝ)) / 2) := by sorry

end HindsightGain.Uniform.Supplement
