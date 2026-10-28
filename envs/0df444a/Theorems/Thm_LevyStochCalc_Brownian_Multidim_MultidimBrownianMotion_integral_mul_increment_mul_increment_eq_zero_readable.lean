-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_mul_increment_mul_increment_eq_zero_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:44.646986+00:00
-- url     : https://prove2.me/theorems/072f3669-7226-4448-b3cd-1af95cb1fa42
-- title:
--   Vanishing Weighted Cross Term on a Common Interval
-- statement:
--   This is the direct cross-orthogonality identity for distinct Brownian coordinates.
--
--   Let $W$ be a $d$-dimensional Brownian motion, let $i\ne j$, and let $\mathcal F$ make every coordinate a Brownian motion. Let $0\le a<b$. If $Z$ is strongly $\mathcal F_a$-measurable, measurable, and bounded in absolute value, then
--   $$
--   \int Z(\omega)(W^i_b-W^i_a)(W^j_b-W^j_a)\,dP=0.
--   $$
--
--   This is the fundamental common-interval cross identity used to establish orthogonality of distinct Brownian coordinates and their Itô integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_mul_increment_mul_increment_eq_zero (W : MultidimBrownianMotion P d) {i j : Fin d}
--       (hij : i ≠ j) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
--       (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
--       {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z) (hZm : Measurable Z) {C : ℝ}
--       (hZb : ∀ ω, |Z ω| ≤ C) :
--       ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityDirectCross`](https://prove2.me/theorems/fd42d764-e99f-4994-8020-f8822509f5ef).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integral_crossSum_sq`](https://prove2.me/theorems/ef40178c-963c-4c39-b6b5-7722afb01efd), [`integral_mul_increment_mul_increment_eq_crossSum`](https://prove2.me/theorems/27178f99-4152-4a50-8019-f02f8e023497).
--
--   Previous: [`integral_mul_increment_mul_increment_eq_crossSum`](https://prove2.me/theorems/27178f99-4152-4a50-8019-f02f8e023497).
--
--   [Source excerpt, lines 307–312](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean#L307-L312) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean#L304-L410 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}

theorem LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero_readable (W : MultidimBrownianMotion P d) {i j : Fin d}
    (hij : i ≠ j) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z) (hZm : Measurable Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P = 0 := by sorry
