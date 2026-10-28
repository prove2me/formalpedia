-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_bounded_mul_lt_top_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:58.616988+00:00
-- url     : https://prove2.me/theorems/fa63e2ae-b5b3-434d-89f7-ccbf3c60fe6e
-- title:
--   Bounded Multipliers Preserve Finite Squared Energy
-- statement:
--   This technical statement shows that a bounded multiplier preserves local square-integrability. Let $H:Ω×ℝ→ℝ$ be such that, for every $T>0$, its iterated squared `ENNReal` energy is strictly below $⊤$. Let $g:Ω×ℝ→ℝ$ and $K_g∈ℝ$ satisfy $0≤K_g$ and $|g(ω,s)|≤K_g$ for all $ω,s$.
--
--   Then, for every $T>0$,
--
--   $$\int_Ω\int_{[0,T]}\|g(ω,s)H(ω,s)\|^2\,ds\,dP<⊤.$$
--
--   The integrals take values in $[0,∞]$ before the strict inequality is imposed. No probability-measure assumption is required for $P$ in this declaration. This lemma supplies the energy estimate needed when multiplying an integrand by bounded coefficients.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_bounded_mul_lt_top
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {g : Ω → ℝ → ℝ} {Kg : ℝ} (hKg0 : 0 ≤ Kg) (hKg : ∀ ω s, |g ω s| ≤ Kg) :
--       ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoMartingaleRiemann`](https://prove2.me/theorems/a19ff47c-1595-4931-a8e8-afa8cea42789).
--
--   [Source excerpt, lines 51–56](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoMartingaleRiemann.lean#L51-L56) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoMartingaleRiemann.lean#L49-L79 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoMartingaleRiemann`, declaration `LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoMartingaleRiemann

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top_readable
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {g : Ω → ℝ → ℝ} {Kg : ℝ} (hKg0 : 0 ≤ Kg) (hKg : ∀ ω s, |g ω s| ≤ Kg) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
