-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:32.220091+00:00
-- url     : https://prove2.me/theorems/b2a75191-454e-466b-aa72-6635b7bb48fd
-- title:
--   Energy Triangle Inequality for Three Integrands
-- statement:
--   This vendored inequality controls the squared energy of a difference through a common third integrand.
--
--   Let $f,g,h:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable, let $P$ be a measure on $\Omega$, and let $T\in\mathbb R$. Then
--
--   $$
--   \int_\Omega\int_{[0,T]}
--   \|f(\omega,s)-g(\omega,s)\|^2\,ds\,dP(\omega)
--   \leq
--   2\left(
--   \int_\Omega\int_{[0,T]}\|f-h\|^2\,ds\,dP
--   +
--   \int_\Omega\int_{[0,T]}\|g-h\|^2\,ds\,dP
--   \right).
--   $$
--
--   The integrals are expressed as `ENNReal` lower integrals, so the estimate also covers infinite values.
--
--   This is a reusable quadratic comparison estimate for coefficient energies.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_energy_sub_le {f g h : Ω → ℝ → ℝ}
--       (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
--       (hh : Measurable (Function.uncurry h)) (T : ℝ) :
--       ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
--         ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--               (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--             + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--               (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionSup`](https://prove2.me/theorems/eac19afb-1a3e-420c-b0c9-4e8c576afefc).
--
--   Previous: [`lintegral_iSup_sq_norm_version_sub_le`](https://prove2.me/theorems/3d71b361-cb18-4a6b-a812-4786fccd9817).
--
--   [Source excerpt, lines 378–385](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionSup.lean#L378-L385) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionSup.lean#L375-L418 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionSup`, declaration `LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionSup

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionSup.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le_readable {f g h : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hh : Measurable (Function.uncurry h)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by sorry
