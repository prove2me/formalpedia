-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_pow_four_eq_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_pow_four_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:01.07553+00:00
-- url     : https://prove2.me/theorems/2e23b33c-826a-4615-a6b9-f62674c63f74
-- title:
--   Fourth Lintegral as an OfReal Fourth Moment
-- statement:
--   This theorem identifies the fourth `lintegral` of an elementary Brownian integral with the `ENNReal.ofReal` of its ordinary fourth moment.
--
--   Let $W$ be a Brownian motion, let $G$ be a simple predictable integrand, and assume that every coefficient satisfies $|\xi_i(\omega)|\le C$. Then
--
--   $$
--   \int^- \left\|\operatorname{simpleIntegral}(W,G,T,\omega)\right\|^4\,dP
--   =\operatorname{ENNReal.ofReal}\!\left(\int \operatorname{simpleIntegral}(W,G,T,\omega)^4\,dP\right).
--   $$
--
--   The left-hand side uses the nonnegative extended-real norm and takes values in $[0,\infty]$; the right-hand side uses the real Lebesgue integral followed by `ENNReal.ofReal`. The result provides the bridge between ordinary moment estimates and `lintegral` estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.lintegral_pow_four_eq {T : ℝ} (G : SimplePredictable Ω T)
--       {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
--       ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
--         = ENNReal.ofReal (∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentLintegral`](https://prove2.me/theorems/e9dd3a38-7a56-4504-970d-056a933b183f).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`abs_clamp_sub_le`](https://prove2.me/theorems/1920857f-1d3d-455c-88bd-4b390cbdc408).
--
--   [Source excerpt, lines 115–118](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean#L115-L118) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean#L114-L141 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentLintegral`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_pow_four_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_pow_four_eq_readable {T : ℝ} (G : SimplePredictable Ω T)
    {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ENNReal.ofReal (∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P) := by sorry
