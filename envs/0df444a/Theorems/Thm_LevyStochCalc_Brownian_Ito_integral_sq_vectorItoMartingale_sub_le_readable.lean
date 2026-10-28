-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_vectorItoMartingale_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_sq_vectorItoMartingale_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:05.781989+00:00
-- url     : https://prove2.me/theorems/d36fc9ed-f7c1-4780-bf4d-334940405111
-- title:
--   Second Moment Bound for a Vector Itô Martingale Increment
-- statement:
--   This is a technical second-moment estimate for a coordinate of a vector Itô martingale.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $W$ be a $d$-dimensional Brownian motion whose coordinates have Brownian filtration $\mathcal F$, and let $H_{mk}(\omega,s)$ be the integrands. Assume that every $H_{mk}$ is measurable and progressively measurable, that its squared norm has finite extended integral on every interval $[0,T]$ with $T>0$, and that there is $C\ge 0$ such that
--   $$
--   |H_{mk}(\omega,s)|\le C
--   $$
--   for all state indices $m\in\operatorname{Fin}(n)$, Brownian indices $k\in\operatorname{Fin}(d)$, $\omega\in\Omega$, and times $s\in\mathbb R$. For $u,v\in\mathbb R$ with $0\le u<v$, the theorem concerns the coordinate $m$ of `vectorItoMartingale`.
--
--   The increment is square-integrable and satisfies
--   $$
--   \int_\Omega \left|M_m(v,\omega)-M_m(u,\omega)\right|^2\,dP(\omega)
--   \le d^2 C^2(v-u),
--   $$
--   where $M_m(t,\omega)$ denotes the corresponding coordinate of `vectorItoMartingale`.
--
--   This estimate is reused as the coordinatewise martingale moment bound for vector Itô-process estimates.
--
--   **Formalization Note** `P` is a probability measure. The finiteness hypothesis is expressed using an `ENNReal` integral, while the conclusion uses the ordinary real integral; `vectorItoMartingale` is the Lean definition involved.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_vectorItoMartingale_sub_le (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
--       Integrable (fun ω => (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
--           - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2) P
--         ∧ ∫ ω, (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
--             - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2 ∂P
--           ≤ (d : ℝ) ^ 2 * (C ^ 2 * (v - u))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integrable_sq_sum_and_le`](https://prove2.me/theorems/d4b79fef-61af-4942-9baf-cd68b6846eef), [`integral_sub_sq_le`](https://prove2.me/theorems/943c5a51-ca07-4807-82e3-773eb2dc5277).
--
--   Previous: [`integrable_abs_add_and_le`](https://prove2.me/theorems/ee1f9d4b-e8aa-494d-8fe1-af42c7a5d32e) · Next: [`integral_abs_vectorItoMartingale_sub_le`](https://prove2.me/theorems/8b157a78-e3e6-4128-ac91-5b7ce7b8fb41).
--
--   [Source excerpt, lines 285–290](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L285-L290) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L283-L324 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integral_sq_vectorItoMartingale_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.integral_sq_vectorItoMartingale_sub_le_readable (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2) P
      ∧ ∫ ω, (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2 ∂P
        ≤ (d : ℝ) ^ 2 * (C ^ 2 * (v - u)) := by sorry
