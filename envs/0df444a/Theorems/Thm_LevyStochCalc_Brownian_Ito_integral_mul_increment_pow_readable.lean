-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_mul_increment_pow_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:30.848544+00:00
-- url     : https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81
-- title:
--   Factorization of a Brownian Increment Power
-- statement:
--   This is an independence factorization for powers of a Brownian increment.
--
--   Let $W$ be a Brownian motion with Brownian filtration $\mathcal F$. Let $0\le a<b$, let $Y:\Omega\to\mathbb R$ be strongly measurable with respect to $\mathcal F_a$ and measurable, and let $m\in\mathbb N$. Then
--   $$
--   \int Y(\omega)\bigl(W_b(\omega)-W_a(\omega)\bigr)^m\,dP
--   =
--   \left(\int Y\,dP\right)
--   \left(\int (W_b-W_a)^m\,dP\right).
--   $$
--
--   This statement formalizes the independence of information available by time $a$ from every power of the increment over $(a,b]$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_increment_pow (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
--       (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
--       ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
--         = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`integral_pow_gaussianReal_zero`](https://prove2.me/theorems/5bcebbba-553a-4972-8595-83ab7dcceb2b) · Next: [`stronglyMeasurable_partialSum`](https://prove2.me/theorems/fd1cc025-8f0a-4737-8e80-8b55eaf193de).
--
--   [Source excerpt, lines 112–116](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean#L112-L116) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentIncrements`, declaration `LevyStochCalc.Brownian.Ito.integral_mul_increment_pow`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean, lines 110-129). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

theorem LevyStochCalc.Brownian.Ito.integral_mul_increment_pow_readable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
    (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
    ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
      = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P := by sorry
