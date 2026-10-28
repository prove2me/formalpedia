-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_weighted_cellSum_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:05.361705+00:00
-- url     : https://prove2.me/theorems/e11cf57f-a8a1-490b-8ae1-d5f30200235a
-- title:
--   First-Moment Bound for a Weighted Finite Cell Sum
-- statement:
--   This is a finite-sum $L^1$ estimate for weighted random variables.
--
--   Let $P$ be a measure on $\Omega$, let $w_i,R_i:\Omega\to\mathbb R$ be measurable for every $i\in\mathbb N$, and let $K_w\ge0$. Assume $|w_i(\omega)|\le K_w$, each $|R_i|$ is integrable, and for some $\rho\in\mathbb R$,
--   $$
--   \int |R_i|\,dP\le\rho\quad\text{for every }i.
--   $$
--   Then the finite sum $\sum_{i<N}w_iR_i$ is integrable and
--   $$
--   \int\left|\sum_{i<N}w_iR_i\right|dP\le N K_w\rho.
--   $$
--
--   This auxiliary lemma packages the triangle inequality and a common first-moment bound for cell-sum estimates; it does not require that $P$ be a probability measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_weighted_cellSum_le (N : ℕ) (w R : ℕ → Ω → ℝ)
--       (hwm : ∀ i, Measurable (w i)) (hRm : ∀ i, Measurable (R i))
--       {Kw : ℝ} (hKw0 : 0 ≤ Kw) (hwb : ∀ (i : ℕ) (ω : Ω), |w i ω| ≤ Kw)
--       (hRint : ∀ i, Integrable (fun ω => |R i ω|) P)
--       {ρ : ℝ} (hRle : ∀ i, ∫ ω, |R i ω| ∂P ≤ ρ) :
--       Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P
--         ∧ ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P ≤ (N : ℝ) * (Kw * ρ)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds`](https://prove2.me/theorems/e506e7f3-bd3b-40cf-9c41-baaea27e3be9).
--
--   Next: [`IsVectorItoVersion.integral_abs_sum_drift_sq_le`](https://prove2.me/theorems/23639e5d-857a-4a6f-b70d-931626366848).
--
--   [Source excerpt, lines 46–52](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean#L46-L52) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean#L42-L77 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le_readable (N : ℕ) (w R : ℕ → Ω → ℝ)
    (hwm : ∀ i, Measurable (w i)) (hRm : ∀ i, Measurable (R i))
    {Kw : ℝ} (hKw0 : 0 ≤ Kw) (hwb : ∀ (i : ℕ) (ω : Ω), |w i ω| ≤ Kw)
    (hRint : ∀ i, Integrable (fun ω => |R i ω|) P)
    {ρ : ℝ} (hRle : ∀ i, ∫ ω, |R i ω| ∂P ≤ ρ) :
    Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P ≤ (N : ℝ) * (Kw * ρ) := by sorry
