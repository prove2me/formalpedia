-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_parallelogram_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_energy_parallelogram_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:09.011524+00:00
-- url     : https://prove2.me/theorems/96c5aee3-d8ba-4423-8ee1-8a16ceb44213
-- title:
--   Parallelogram Law for Itô Integrand Energies
-- statement:
--   This vendored statement is the pointwise parallelogram law for squared Itô-integrand energies.
--
--   Let $(\Omega,P)$ be a measurable space with measure $P$, and let $H_1,H_2:\Omega\times\mathbb R\to\mathbb R$ have measurable uncurried forms. For every $T\in\mathbb R$, the double `ENNReal` energy integrals over $\Omega$ and the interval $[0,T]$ satisfy
--
--   $$
--   \begin{aligned}
--   &\int_\Omega\int_{[0,T]}
--   \|H_1(\omega,s)+H_2(\omega,s)\|_e^2\,ds\,dP\\
--   &\quad+
--   \int_\Omega\int_{[0,T]}
--   \|H_1(\omega,s)-H_2(\omega,s)\|_e^2\,ds\,dP\\
--   &=2\int_\Omega\int_{[0,T]}
--   \|H_1(\omega,s)\|_e^2\,ds\,dP
--   +2\int_\Omega\int_{[0,T]}
--   \|H_2(\omega,s)\|_e^2\,ds\,dP.
--   \end{aligned}
--   $$
--
--   The identity holds without a probability-measure assumption and uses extended nonnegative integrals, so both sides may be infinite. It is the energy-level algebraic input for proving additivity of the associated $L^2$ Itô integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_energy_parallelogram (hm₁ : Measurable (Function.uncurry H₁))
--       (hm₂ : Measurable (Function.uncurry H₂)) (T : ℝ) :
--       (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--           + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
--         = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--           + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a).
--
--   Next: [`lintegral_energy_lt_top_of_bound`](https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315).
--
--   [Source excerpt, lines 61–66](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean#L61-L66) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLinear.lean#L59-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLinear`, declaration `LevyStochCalc.Brownian.Ito.lintegral_energy_parallelogram`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable {H₁ H₂ : Ω → ℝ → ℝ}
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.lintegral_energy_parallelogram_readable (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂)) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
