-- Prove2me | Theorems.Thm_OnlineUBSR_Supplement_theorem_6
-- name    : OnlineUBSR.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:38:27.069799+00:00
-- url     : https://prove2.me/theorems/c4395b47-1b59-4442-8eb1-0d9ef05eee44
-- title:
--   Theorem 6 (corrected: base assumptions and uniform constants) — phased projected-SGD bound
-- statement:
--   Under Assumptions 1–9, 11, and 12, run the projected recursion (18) for $n\ge4$ iterations with the phase boundaries (19), step sizes $b_k=b_0 2^{-i}/\sqrt n$, and batch sizes $m_k=2^i n$ on phase $i$. Then
--   $$
--   \mathbb E[h(\theta_n)-h(\theta^*)]\le \frac{K_2}{\sqrt n}+\frac{K_3}{n}+\frac{K_4}{n^{3/2}},
--   $$
--   with $K_2,K_3,K_4$ and $B_1$ exactly as printed in (21).
--
--   Differences from the source:
--   - correction: Lemmas 3–5 omit Assumptions 4–6 used by this theorem → Lean requires the complete Assumptions 1–9; reason: the printed theorem itself says Assumptions 1–9 and its constants depend on them
--   - correction: the inner assumptions use the flawed Assumption 3, noise starting at one, and unrestricted $t_0$ → Lean carries the three corrections of Theorem 1; reason: every derivative estimate contains the inner projected estimator
--   - reading: $C_4,C_5$ are fixed-parameter constants → Lean takes the initial-error supremum over the interval and evaluates $K_1$ at $m=n$; reason: $m_k\ge n$ and the estimator is evaluated at random $\theta_k$
--   - encoding: $p=\inf\{i:2^{-i}n\le1\}$ and $n_i=n-\lceil2^{-i}n\rceil$ → Lean uses a least-index predicate and natural phase boundaries with $n_{p+1}=n$; reason: this is the exact schedule without an empty-infimum default
--   - encoding: Assumption 11 writes $h''\ge0$ → Lean also states differentiability of $h$ and $h'$; reason: this prevents default derivatives from trivializing convexity
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 6, p.12, equations (19)–(21)

import Mathlib
import Definitions.Def_OnlineUBSR_Supplement_Model

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR.Supplement

/-- **Theorem 6 (last-iterate bound for phased projected SGD).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 6, p.12, (19)--(21).

**Formalization Note.** `phaseStart` and `IsPhaseCount` encode (19), including the ceiling and
the least phase index; `n_{p+1}=n` is the final branch in `hschedule`. `C₄,C₅` are uniform over
the random iterates, with `K₁` evaluated at `m=n`, since every scheduled batch is at least `n`.
The three base corrections and the restored Assumptions 4--6 used by Lemmas 3--5 are explicit. -/
theorem theorem_6
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
    (n : ℕ) (hn : 4 ≤ n) (p : ℕ) (hp : IsPhaseCount n p)
    (b₀ : ℝ) (hb₀ : 0 < b₀) (b : ℕ → ℝ) (m : ℕ → ℕ)
    (hschedule : ∀ k, 1 ≤ k → k ≤ n →
      ∃ i ≤ p,
        phaseStart n i < k ∧ k ≤ (if i = p then n else phaseStart n (i + 1)) ∧
        b k = b₀ * (2 : ℝ) ^ (-(i : ℝ)) / Real.sqrt n ∧ m k = 2 ^ i * n) :
    let θit := projectedSGD M S θ₁ b m
    ∫ ω, objective M (θit n ω) - objective M θstar ∂μ ≤
      (4 * D ^ 2 / b₀ + 39 * D * C4Uniform M n + 11 * B1 M ^ 2 * b₀) /
          Real.sqrt n +
        16 * b₀ * B1 M * C4Uniform M n / n +
        (20 * C5Uniform M n * b₀ / 3) / (n : ℝ) ^ (3 / 2 : ℝ) := by sorry

end OnlineUBSR.Supplement
