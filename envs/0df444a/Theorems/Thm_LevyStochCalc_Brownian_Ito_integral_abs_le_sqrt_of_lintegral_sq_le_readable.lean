-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_le_sqrt_of_lintegral_sq_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_le_sqrt_of_lintegral_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:21.767806+00:00
-- url     : https://prove2.me/theorems/fabb0c45-93fb-4537-bc15-bc10719aac9e
-- title:
--   First-Moment Bound from an Extended $L^2$ Bound
-- statement:
--   This is a probability-space $L^2$-to-$L^1$ estimate.
--
--   Let $P$ be a probability measure on $\Omega$, let $g:\Omega\to\mathbb R$ be almost everywhere strongly measurable, and let $V\ge0$. If
--   $$
--   \int_\Omega \|g(\omega)\|^2\,dP(\omega)\le \operatorname{ofReal}(V),
--   $$
--   where the left side is the extended nonnegative integral, then $g$ is integrable and
--   $$
--   \int_\Omega |g(\omega)|\,dP(\omega)\le\sqrt V.
--   $$
--
--   This is a reusable conversion from an extended-valued squared-moment estimate to integrability and an ordinary first-moment estimate.
--
--   **Formalization Note** The hypothesis uses `ENNReal` and `ENNReal.ofReal`; the conclusion uses the ordinary integral and `Real.sqrt`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_le_sqrt_of_lintegral_sq_le {P : Measure Ω} [IsProbabilityMeasure P]
--       {g : Ω → ℝ} (hg : MeasureTheory.AEStronglyMeasurable g P) {V : ℝ} (hV0 : 0 ≤ V)
--       (hle : ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal V) :
--       MeasureTheory.Integrable g P ∧ ∫ ω, |g ω| ∂P ≤ Real.sqrt V
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFormulaScalar`](https://prove2.me/theorems/58932039-f65d-4b41-a617-bf3796b6492d).
--
--   Supporting theorems: [`integral_abs_le_sqrt_of_integral_sq_le`](https://prove2.me/theorems/bfdc1797-b9af-45f2-9493-fd8068fd1149).
--
--   [Source excerpt, lines 52–55](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFormulaScalar.lean#L52-L55) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFormulaScalar.lean#L51-L73 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFormulaScalar`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_le_sqrt_of_lintegral_sq_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaScalar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaScalar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.integral_abs_le_sqrt_of_lintegral_sq_le_readable {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.AEStronglyMeasurable g P) {V : ℝ} (hV0 : 0 ≤ V)
    (hle : ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal V) :
    MeasureTheory.Integrable g P ∧ ∫ ω, |g ω| ∂P ≤ Real.sqrt V := by sorry
