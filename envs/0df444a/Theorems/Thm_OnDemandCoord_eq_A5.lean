-- Prove2me | Theorems.Thm_OnDemandCoord_eq_A5
-- name    : OnDemandCoord.eq_A5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:18.066107+00:00
-- url     : https://prove2.me/theorems/5fe88ee2-977c-47c2-9633-4da5b7e9eac0
-- title:
--   (A.5): $g(U)=\mathbb E[\min\{S,\sum_{U}\hat X_i\}]$ is a rank function and LP (8) has value $g(I)$
-- statement:
--   **(A.5)** (pp. A6–A7). For any staffing levels $Q$ and workforce $S\ge0$, the set function
--   $$g(U)=\mathbb E\Big[\min\Big\{S,\sum_{i\in U}(X_i-Q_i)^+\Big\}\Big]$$
--   is a rank function ($g(\emptyset)=0$, nondecreasing, submodular), and every optimal solution $\beta^*$ of the linear program (8) at $(Q,S)$ satisfies
--   $$\sum_{i\in I}\beta^*_i\,\mathbb E[(X_i-Q_i)^+]=\mathbb E\Big[\min\Big\{S,\sum_{i\in I}(X_i-Q_i)^+\Big\}\Big].$$
--
--   With the no-waste property of the TFRB policy this turns the inequalities of Step 1 into equalities at an optimal $\beta^*$.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - generalization: stated for the LP (8) after rescaling β̂_i = β_i E[(X_i − Q_i)⁺], implicitly with E[(X_i − Q_i)⁺] > 0 → every Q and S ≥ 0, firms with E[(X_i − Q_i)⁺] = 0 allowed; reason: such firms have g({i}) = 0, so the identity is unchanged; it specializes to the paper's case
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), (A.5) and the preceding paragraph, pp. A6–A7 (PDF 38–39)

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **(A.5)**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), pp. A6–A7 (PDF 38–39). For any `Q` and `s ≥ 0`, the set function
`g(U) = E[min {s, ∑_{i ∈ U} (X_i − Q_i)⁺}]` is a rank function, and every optimal `β` of (8) has
`∑_i β_i E[(X_i − Q_i)⁺] = E[min {s, ∑_i (X_i − Q_i)⁺}]`. -/
theorem eq_A5 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Q : Fin n → ℝ) (s : ℝ) (hs : 0 ≤ s) :
    Disjunctive.Polymatroids.IsPolymatroidRankFunction (M.rankFn Q s) ∧
      ∀ β, M.IsOptimalLP Q s β →
        ∑ i, β i * M.mean Q i = ∫ ω, min s (∑ i, M.vac Q i ω) ∂P := by sorry

end OnDemandCoord
