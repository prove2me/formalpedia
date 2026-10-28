-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_lt_top_of_bound_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:13.976896+00:00
-- url     : https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315
-- title:
--   Finite Energy Under Quadratic Domination
-- statement:
--   This vendored technical lemma proves finiteness of a square-integrated energy under pointwise domination.
--
--   Let $\Omega$ be a measurable space with measure $P$, and let $H_1,H_2,K:\Omega\times\mathbb R\to\mathbb R$. Assume:
--
--   1. For every $(\omega,s)$,
--
--   $$
--   \|K(\omega,s)\|_e^2
--   \leq 2\left(\|H_1(\omega,s)\|_e^2+\|H_2(\omega,s)\|_e^2\right).
--   $$
--
--   2. The uncurried functions $H_1$ and $H_2$ are measurable.
--   3. For every $T>0$, the double `ENNReal` energy integrals of $H_1$ and $H_2$ over $\Omega\times[0,T]$ are strictly below $\infty$.
--
--   Then, for every $T>0$, the corresponding double energy integral of $K$ is also strictly below $\infty$:
--
--   $$
--   \int_\Omega\int_{[0,T]}
--   \|K(\omega,s)\|_e^2\,ds\,dP(\omega)<\infty.
--   $$
--
--   No probability-measure instance is required by the theorem. This is a technical integrability tool for Itô-integrand constructions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_energy_lt_top_of_bound {K : Ω → ℝ → ℝ}
--       (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
--         ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2))
--       (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
--       (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
--       ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a).
--
--   Previous: [`lintegral_energy_parallelogram`](https://prove2.me/theorems/96c5aee3-d8ba-4423-8ee1-8a16ceb44213) · Next: [`lintegral_energy_const_mul`](https://prove2.me/theorems/ce857bc0-8f4c-4f64-b3bd-5184a06ec375).
--
--   [Source excerpt, lines 104–113](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean#L104-L113) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLinear.lean#L101-L135 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLinear`, declaration `LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound_readable {K : Ω → ℝ → ℝ}
    (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2))
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
