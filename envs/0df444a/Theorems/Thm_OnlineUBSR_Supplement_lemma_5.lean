-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_lemma_5
-- name    : OnlineUBSR.Supplement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:37:54.249699+00:00
-- url     : https://prove2.me/theorems/c94bb901-45d3-488d-afa2-3f3e54f3570c
-- title:
--   Lemma 5 (corrected: restored Assumptions 4–6) — constant-step projected-SGD sum
-- statement:
--   With constant step size $b>0$ and constant batch size $m\ge1$, the projected recursion satisfies
--   $$
--   \sum_{k=1}^n\mathbb E[h(\theta_k)-h(\theta^*)]\le
--   \frac{D^2}{2b}+2nD\frac{C_4}{\sqrt m}+\frac{nbB_1^2}{2},
--   $$
--   where $\theta^*$ is a minimizer of $h$ over the printed interval.
--
--   Differences from the source:
--   - correction: the printed lemma omits Assumptions 4–6 → Lean restores them; reason: $C_4$ comes from Lemma 1
--   - correction: the inner assumptions use the flawed Assumption 3, noise starting at one, and unrestricted $t_0$ → Lean carries the three corrections of Theorem 1; reason: the derivative-estimator bound depends on them
--   - reading: $C_4$ is written at a fixed parameter → Lean uses the uniform interval constant; reason: it is applied at random iterates
--   - encoding: $\theta^*$ denotes the solution of (9) → Lean requires membership in the interval and the minimizer inequality; reason: this constructs the source's object instead of taking an unrelated point
--   - encoding: smooth convex objective → differentiable $h,h'$ and $h''\ge0$; reason: this is the source's Assumption 11 in derivative form
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 5, p.31, equation (69)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real Finset

namespace OnlineUBSR.Supplement

/-- **Lemma 5 (constant-step regret sum for projected SGD).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 5, p.31, (69).

**Formalization Note.** The printed lemma omits Assumptions 4--6 although `C₄` comes from
Lemma 1; they are restored. `θ*` is a minimizer of the source's problem (9), not an unrelated
point. The sum is over the one-based projected iterates. -/
theorem lemma_5
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model E) [IsProbabilityMeasure M.ν]
    (S : Bool → ℕ → ℕ → Ω → E) (hbank : IsSampleBank μ M S)
    (h123 : Assumptions1To3 M) (h59 : Assumptions5To9 M)
    (hsmooth : SmoothObjective M)
    (hA4 : ∀ outer θ, θ ∈ Set.Icc M.θl M.θu → InnerNoiseBound μ M S outer θ)
    (hA11 : ∀ θ ∈ Set.Icc M.θl M.θu, 0 ≤ deriv (deriv (objective M)) θ)
    (D : ℝ) (hD : 0 < D)
    (hA12 : ∀ θ₁ ∈ Set.Icc M.θl M.θu, ∀ θ₂ ∈ Set.Icc M.θl M.θu, |θ₁ - θ₂| ≤ D)
    (θstar : ℝ) (hθstar : θstar ∈ Set.Icc M.θl M.θu)
    (hmin : ∀ θ ∈ Set.Icc M.θl M.θu, objective M θstar ≤ objective M θ)
    (θ₁ : ℝ) (hθ₁ : θ₁ ∈ Set.Icc M.θl M.θu)
    (b : ℝ) (hb : 0 < b) (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 1 ≤ n) :
    let θit := projectedSGD M S θ₁ (fun _ => b) (fun _ => m)
    ∑ k ∈ Icc 1 n, (∫ ω, objective M (θit k ω) - objective M θstar ∂μ) ≤
      D ^ 2 / (2 * b) + 2 * n * D * (C4Uniform M m / Real.sqrt m) +
        n * b * B1 M ^ 2 / 2 := by sorry

end OnlineUBSR.Supplement
