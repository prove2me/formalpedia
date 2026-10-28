-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integrable_cross_term_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:23.588265+00:00
-- url     : https://prove2.me/theorems/7e5b804f-7b35-4962-9762-372081226c2c
-- title:
--   Integrability of Bounded-Coefficient Brownian Cross Terms
-- statement:
--   This is an integrability estimate for a product of two Brownian increments with bounded coefficients.
--
--   Let $P$ be a probability measure, let $V_1,V_2$ be Brownian motions, and let $0\le p\le q$ and $0\le r\le v$. Let $\xi,\eta:\Omega\to\mathbb R$ be measurable and assume $|\xi(\omega)|\le M_\xi$ and $|\eta(\omega)|\le M_\eta$. Then
--   $$
--   \omega\mapsto \bigl(\xi(\omega)(V_1(q,\omega)-V_1(p,\omega))\bigr)
--   \bigl(\eta(\omega)(V_2(v,\omega)-V_2(r,\omega))\bigr)
--   $$
--   is integrable.
--
--   The result is a technical domination lemma for cross terms; it asserts integrability but no vanishing or orthogonality conclusion.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma integrable_cross_term (V₁ V₂ : BrownianMotion P) {p q r v : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
--       (hr : 0 ≤ r) (hrv : r ≤ v) {ξ η : Ω → ℝ} (hξm : Measurable ξ) (hηm : Measurable η)
--       {Mξ Mη : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hηb : ∀ ω, |η ω| ≤ Mη) :
--       Integrable (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω))
--         * (η ω * (V₂.W v ω - V₂.W r ω))) P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityLimit`](https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74).
--
--   Definition modules: [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Next: [`integral_cross_increment_eq_zero_of_le`](https://prove2.me/theorems/cad27d60-eab1-4df3-bc16-26fa2ac60f01).
--
--   [Source excerpt, lines 55–59](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L55-L59) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L54-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable (V₁ V₂ : BrownianMotion P) {p q r v : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hr : 0 ≤ r) (hrv : r ≤ v) {ξ η : Ω → ℝ} (hξm : Measurable ξ) (hηm : Measurable η)
    {Mξ Mη : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hηb : ∀ ω, |η ω| ≤ Mη) :
    Integrable (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω))
      * (η ω * (V₂.W v ω - V₂.W r ω))) P := by sorry
