-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_const_mul_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:35.640002+00:00
-- url     : https://prove2.me/theorems/ce857bc0-8f4c-4f64-b3bd-5184a06ec375
-- title:
--   Scaling Law for Integrand Energy
-- statement:
--   This statement gives the exact energy scaling law. Let $H:Ω×ℝ→ℝ$ be jointly measurable, let $c,T∈ℝ$, and let $P$ be a measure. Then
--
--   $$\int_Ω\int_{[0,T]}\|cH(ω,s)\|^2\,ds\,dP
--   =\operatorname{ofReal}(c^2)\,\int_Ω\int_{[0,T]}\|H(ω,s)\|^2\,ds\,dP.$$
--
--   Both sides are `ENNReal` values in $[0,∞]$; the scalar factor is `ENNReal.ofReal (c ^ 2)`. No positivity assumption on $T$ and no probability-measure assumption on $P$ is present. This identity is used to verify the energy hypotheses under scalar multiplication.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_energy_const_mul {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
--       (c T : ℝ) :
--       (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--         = ENNReal.ofReal (c ^ 2)
--           * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a).
--
--   Previous: [`lintegral_energy_lt_top_of_bound`](https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315) · Next: [`ae_eq_add_of_sq_distances`](https://prove2.me/theorems/99e33505-e2ff-46c1-a724-6a8f67657125).
--
--   [Source excerpt, lines 155–159](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLinear.lean#L155-L159) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLinear.lean#L153-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLinear`, declaration `LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul_readable {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (c T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
