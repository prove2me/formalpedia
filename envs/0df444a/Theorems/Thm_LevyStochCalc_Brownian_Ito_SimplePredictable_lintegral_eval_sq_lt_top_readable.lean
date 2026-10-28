-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_lintegral_eval_sq_lt_top_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_sq_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:41.924461+00:00
-- url     : https://prove2.me/theorems/1a3d860d-d849-45a8-9155-ad2dbfbcdfa6
-- title:
--   Finite Squared Energy of a Simple Integrand
-- statement:
--   Let $G$ be a simple predictable integrand on a probability space $(Ω,P)$, and let $T'>0$. Then its evaluation has finite squared `ENNReal` energy on $[0,T']$:
--
--   $$\int_Ω\int_{[0,T']}\|G(s,ω)\|^2\,ds\,dP<⊤.$$
--
--   The integral is an iterated integral with values in $[0,∞]$, and the conclusion is strict finiteness. This lemma records the uniform boundedness consequence that makes simple integrands admissible for the `L²` Brownian Itô integral.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.lintegral_eval_sq_lt_top {T : ℝ} (G : SimplePredictable Ω T)
--       (P : Measure Ω) [IsProbabilityMeasure P] (T' : ℝ) (_hT' : 0 < T') :
--       ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand`](https://prove2.me/theorems/09c55224-b261-4948-9982-f2ec68361149).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb).
--
--   Next: [`simpleIntegral_diff_isometry_of_adapted`](https://prove2.me/theorems/2683d1bc-8d01-4352-8fe2-981705a37ca4).
--
--   [Source excerpt, lines 40–43](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean#L40-L43) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean#L39-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_sq_lt_top`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_sq_lt_top_readable {T : ℝ} (G : SimplePredictable Ω T)
    (P : Measure Ω) [IsProbabilityMeasure P] (T' : ℝ) (_hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
