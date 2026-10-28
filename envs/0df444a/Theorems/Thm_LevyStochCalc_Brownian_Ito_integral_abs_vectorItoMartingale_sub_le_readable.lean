-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_vectorItoMartingale_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_vectorItoMartingale_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:02.02099+00:00
-- url     : https://prove2.me/theorems/8b157a78-e3e6-4128-ac91-5b7ce7b8fb41
-- title:
--   First Absolute Moment of a Vector Itô Martingale Increment
-- statement:
--   This is a coordinatewise first-moment estimate for the martingale part of a vector Itô process.
--
--   Let $P$ be a probability measure, let $W$ be a $d$-dimensional Brownian motion whose coordinates share a filtration $\mathcal F$, and let $H_{mk}$ be measurable, progressively measurable, and square-integrable on every positive time interval. Assume $C\ge0$ and $|H_{mk}(\omega,s)|\le C$ for every output coordinate $m\in\mathrm{Fin}(n)$, Brownian coordinate $k\in\mathrm{Fin}(d)$, $\omega$, and $s$. For $m\in\mathrm{Fin}(n)$ and $0\le u<v$, let $M^m_t=\texttt{vectorItoMartingale}(W,\mathcal F,H,m,t)$.
--
--   Then $M^m_v-M^m_u$ is integrable in absolute value and
--   $$
--   \int |M^m_v-M^m_u|\,dP\le d\,C\sqrt{v-u}.
--   $$
--
--   This is a technical coordinate estimate obtained by summing the scalar bounds over the $d$ driving Brownian coordinates.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_vectorItoMartingale_sub_le (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
--       Integrable (fun ω => |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
--           - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω|) P
--         ∧ ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
--             - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω| ∂P
--           ≤ (d : ℝ) * (C * Real.sqrt (v - u))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integrable_abs_sum_and_le`](https://prove2.me/theorems/17bd37cc-5804-4e07-8559-5fe19077a354), [`integral_abs_sub_stochasticIntegral_le`](https://prove2.me/theorems/b9104289-b232-47cf-94d1-9015281546b4).
--
--   Previous: [`integral_sq_vectorItoMartingale_sub_le`](https://prove2.me/theorems/d36fc9ed-f7c1-4780-bf4d-334940405111) · Next: [`measurable_vectorItoProcess_sub`](https://prove2.me/theorems/a8a3a0c4-bf0d-4b14-81c4-23f97e4dcb97).
--
--   [Source excerpt, lines 328–333](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L328-L333) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L326-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_vectorItoMartingale_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.integral_abs_vectorItoMartingale_sub_le_readable (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω|) P
      ∧ ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω| ∂P
        ≤ (d : ℝ) * (C * Real.sqrt (v - u)) := by sorry
