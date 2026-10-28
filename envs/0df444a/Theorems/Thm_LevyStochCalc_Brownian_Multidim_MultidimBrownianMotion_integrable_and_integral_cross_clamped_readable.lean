-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integrable_and_integral_cross_clamped_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_and_integral_cross_clamped_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:59.343452+00:00
-- url     : https://prove2.me/theorems/79cd0607-bfb0-45c8-8086-36a38db2872c
-- title:
--   Integrable Clamped Cross Term with Zero Mean
-- statement:
--   This is an integrability and zero-mean statement for time-clamped Brownian cross terms.
--
--   Let $W$ be a $d$-dimensional Brownian motion with distinct coordinates $i\ne j$, and let $\mathcal F$ make every coordinate a Brownian motion. Assume $0\le p<q$ and $0\le r<v$. Let $\xi$ and $\eta$ be bounded, measurable, and strongly measurable with respect to $\mathcal F_p$ and $\mathcal F_r$, respectively. For arbitrary $t,t'\in\mathbb R$, define the clamped increments using $\min(q,t)-\min(p,t)$ and $\min(v,t')-\min(r,t')$. The resulting product is integrable and
--   $$
--   \int \bigl(\xi(W^i_{\min(q,t)}-W^i_{\min(p,t)})\bigr)
--   \bigl(\eta(W^j_{\min(v,t')}-W^j_{\min(r,t')})\bigr)\,dP=0.
--   $$
--
--   This lemma handles the individual terms appearing when simple stochastic integrals are expanded into partition sums.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma integrable_and_integral_cross_clamped (W : MultidimBrownianMotion P d)
--       {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
--       (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
--       (hpq : p < q)
--       (hr : 0 ≤ r) (hrv : r < v) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
--       (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
--       (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
--       {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
--       Integrable (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
--         * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) P
--       ∧ ∫ ω, (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
--         * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω)) ∂P = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityLimit`](https://prove2.me/theorems/0a6cdcb3-be60-427a-8dc0-4862ed142b74).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integrable_cross_term`](https://prove2.me/theorems/7e5b804f-7b35-4962-9762-372081226c2c), [`integral_cross_increment_eq_zero_of_le`](https://prove2.me/theorems/cad27d60-eab1-4df3-bc16-26fa2ac60f01).
--
--   Previous: [`integral_cross_increment_eq_zero_of_le`](https://prove2.me/theorems/cad27d60-eab1-4df3-bc16-26fa2ac60f01) · Next: [`integral_simpleIntegral_mul_eq_zero`](https://prove2.me/theorems/86d5362c-5613-4331-b577-05629cdbfba1).
--
--   [Source excerpt, lines 210–221](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L210-L221) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean#L209-L236 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityLimit`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_and_integral_cross_clamped`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_and_integral_cross_clamped_readable (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hpq : p < q)
    (hr : 0 ≤ r) (hrv : r < v) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
    (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
    Integrable (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) P
    ∧ ∫ ω, (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω)) ∂P = 0 := by sorry
