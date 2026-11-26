-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_lemma_4
-- name    : OnlineUBSR.Supplement.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:37:18.082251+00:00
-- url     : https://prove2.me/theorems/7b33fcd5-3989-42fe-8873-c6a8c2f04ac8
-- title:
--   Lemma 4 (corrected: restored Assumptions 4–6) — projected-SGD window inequality
-- statement:
--   For the projected recursion (18), any $1<k_0<k_1\le n$ satisfies
--   $$
--   \sum_{k=k_0}^{k_1}2b_k\,\mathbb E[h(\theta_k)-h(\theta_{k_0})]
--   \le\sum_{k=k_0}^{k_1}(2b_kDA_k+b_k^2B_k),
--   $$
--   where $A_k=C_4/\sqrt{m_k}$ and $B_k=C_5/m_k+2B_1A_k+B_1^2$.
--
--   Differences from the source:
--   - correction: the printed lemma omits Assumptions 4–6 → Lean restores them; reason: the proof uses Lemmas 1 and 3 and their constants
--   - correction: the inner estimation assumptions are printed with the flawed Assumption 3, noise starting at one, and unrestricted $t_0$ → Lean carries the three corrections of Theorem 1; reason: every $A_k,B_k$ application uses the corrected inner estimate
--   - reading: $C_4,C_5$ are written at a fixed parameter → Lean uses uniform constants over the parameter interval; reason: $\theta_k$ is random
--   - encoding: “step size” and “batch size” → positive $b_k$ and $m_k\ge1$; reason: this makes every printed division and estimator defined on its intended domain
--   - encoding: smooth convex objective → differentiable $h,h'$ and $h''\ge0$ on the interval; reason: this is the paper's derivative formulation of Assumption 11
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 4, p.30, equation (65)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real Finset

namespace OnlineUBSR.Supplement

/-- **Lemma 4 (window inequality for projected SGD).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Lemma 4, p.30, (65).

**Formalization Note.** Assumptions 4--6, omitted from the printed lemma but required by its
use of Lemmas 1 and 3, are restored. `θ₁` is the initial projected iterate and indices begin at
one. Positive step sizes and nonzero batch sizes unpack the paper's terms “step-size” and
“batch size.” -/
theorem lemma_4
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
    (θ₁ : ℝ) (hθ₁ : θ₁ ∈ Set.Icc M.θl M.θu)
    (b : ℕ → ℝ) (hb : ∀ k, 1 ≤ k → 0 < b k)
    (m : ℕ → ℕ) (hm : ∀ k, 1 ≤ k → 1 ≤ m k)
    (n k₀ k₁ : ℕ) (hk₀ : 1 < k₀) (hk₁ : k₀ < k₁) (hk₁n : k₁ ≤ n) :
    let θit := projectedSGD M S θ₁ b m
    ∑ k ∈ Icc k₀ k₁, 2 * b k *
        (∫ ω, objective M (θit k ω) - objective M (θit k₀ ω) ∂μ) ≤
      ∑ k ∈ Icc k₀ k₁,
        (2 * b k * D * (C4Uniform M (m k) / Real.sqrt (m k)) +
          b k ^ 2 * (C5Uniform M (m k) / m k +
            2 * B1 M * (C4Uniform M (m k) / Real.sqrt (m k)) + B1 M ^ 2)) := by sorry

end OnlineUBSR.Supplement
