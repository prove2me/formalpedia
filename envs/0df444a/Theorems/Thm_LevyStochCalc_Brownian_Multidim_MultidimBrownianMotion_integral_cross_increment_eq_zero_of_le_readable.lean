-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_cross_increment_eq_zero_of_le_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:58.229256+00:00
-- url     : https://prove2.me/theorems/cad27d60-eab1-4df3-bc16-26fa2ac60f01
-- title:
--   Vanishing Cross Term with Ordered Starting Times
-- statement:
--   This is a cross-orthogonality identity when the second interval starts no earlier than the first coefficient's reference time.
--
--   Let $W$ be a $d$-dimensional Brownian motion with distinct coordinates $i\ne j$, and let $\mathcal F$ make every coordinate a Brownian motion. Assume $p,r\ge0$, $p\le r< v$. Let $\xi$ be bounded, measurable, and strongly $\mathcal F_p$-measurable; let $\eta$ be bounded, measurable, and strongly $\mathcal F_r$-measurable. Then
--   $$
--   \int \bigl(\xi(W^i_q-W^i_p)\bigr)
--   \bigl(\eta(W^j_v-W^j_r)\bigr)\,dP=0.
--   $$
--
--   The endpoint $q$ is unrestricted; the result covers both relative positions of $q$ and $r$ by splitting the first increment when necessary.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_cross_increment_eq_zero_of_le (W : MultidimBrownianMotion P d)
--       {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
--       (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
--       (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
--       (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
--       (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
--       ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
--         * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityLimit`](https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integral_mul_increment_pow`](https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81), [`integral_pow_gaussianReal_zero`](https://prove2.me/theorems/5bcebbba-553a-4972-8595-83ab7dcceb2b), [`integrable_cross_term`](https://prove2.me/theorems/7e5b804f-7b35-4962-9762-372081226c2c), [`integral_mul_increment_mul_increment_eq_zero`](https://prove2.me/theorems/072f3669-7226-4448-b3cd-1af95cb1fa42).
--
--   Previous: [`integrable_cross_term`](https://prove2.me/theorems/7e5b804f-7b35-4962-9762-372081226c2c) · Next: [`integrable_and_integral_cross_clamped`](https://prove2.me/theorems/79cd0607-bfb0-45c8-8086-36a38db2872c).
--
--   [Source excerpt, lines 85–92](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L85-L92) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L84-L190 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}

theorem LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le_readable (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by sorry
