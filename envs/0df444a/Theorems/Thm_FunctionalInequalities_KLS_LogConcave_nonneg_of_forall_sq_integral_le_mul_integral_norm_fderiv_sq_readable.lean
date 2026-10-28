-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:40.74592+00:00
-- url     : https://prove2.me/theorems/b98a51cc-c659-42c7-9c41-59b73de13a36
-- title:
--   Nonnegativity Of A Compact-Test Dual Constant
-- statement:
--   This theorem states the sign condition needed for a compact-test dual gradient bound.
--
--   Let $n\ge1$, let $m$ be an additive Haar measure on $E=\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$, let $\nu$ be a probability measure, and let $W:E\to\mathbb R$ be continuous with $\nu=m.\operatorname{tilted}(-W)$. If $F:E\to\mathbb R$ and $K\in\mathbb R$ satisfy, for every smooth compactly supported $h$,
--
--   $$
--   \left(\int_E Fh\,d\nu\right)^2
--   \le
--   K\int_E\|Dh\|^2\,d\nu,
--   $$
--
--   then
--
--   $$
--   0\le K.
--   $$
--
--   The conclusion requires positive dimension $n\ge1$ and uses no convexity assumption on $W$. The derivative is the Fréchet derivative `fderiv ℝ h` and the energy has no factor $1/2$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq {n : ℕ} (hn : 0 < n)
--       (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
--       {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
--       {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
--       (hW : Continuous W) {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ}
--       (hK : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
--         (∫ x, F x * h x ∂(ν : Measure _)) ^ 2 ≤
--           K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
--       0 ≤ K
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HminusOne`](https://prove2.me/theorems/4dc71c7a-51b5-45a0-8de3-41cf287dbc05).
--
--   Next: [`sum_integral_norm_fderiv_partial_sq_le_integral_weightedLaplacian_sq`](https://prove2.me/theorems/34cc3097-b38d-4f33-9bd3-39c1af8e4e9d).
--
--   [Source excerpt, lines 30–38](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean#L30-L38) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean#L26-L174 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HminusOne`, declaration `FunctionalInequalities.KLS.LogConcave.nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HminusOne

open MeasureTheory
open scoped ContDiff

theorem FunctionalInequalities.KLS.LogConcave.nonneg_of_forall_sq_integral_le_mul_integral_norm_fderiv_sq_readable {n : ℕ} (hn : 0 < n)
    (m : Measure (EuclideanSpace ℝ (Fin n))) [m.IsAddHaarMeasure]
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} (hνW : (ν : Measure _) = m.tilted (-W))
    (hW : Continuous W) {F : EuclideanSpace ℝ (Fin n) → ℝ} {K : ℝ}
    (hK : ∀ h : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      (∫ x, F x * h x ∂(ν : Measure _)) ^ 2 ≤
        K * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(ν : Measure _)) :
    0 ≤ K := by sorry
