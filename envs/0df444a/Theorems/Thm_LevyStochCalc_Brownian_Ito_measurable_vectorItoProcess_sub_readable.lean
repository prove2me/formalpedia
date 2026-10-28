-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_measurable_vectorItoProcess_sub_readable
-- name    : LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:44.351494+00:00
-- url     : https://prove2.me/theorems/a8a3a0c4-bf0d-4b14-81c4-23f97e4dcb97
-- title:
--   Measurability of a Vector Itô-Process Increment
-- statement:
--   This is a measurability statement for increments of a vector Itô process.
--
--   Let $P$ be a probability measure, let $W$ be a $d$-dimensional Brownian motion with coordinate Brownian filtrations, let $H_{mk}$ satisfy the stated measurability, progressive-measurability, and $\mathrm{ENNReal}$ square-integrability conditions, and let $X_0:\Omega\to\mathrm{Fin}(n)\to\mathbb R$ and $b_m:\Omega\times\mathbb R\to\mathbb R$ be the initial state and drift coordinates. Assume each $b_m$ is jointly measurable and that there is $B\in\mathbb R$ with $|b_m(\omega,s)|\le B$ for every $m,\omega,s$. For $0\le u\le v$, the increment is
--   $$
--   \omega\mapsto X_v(\omega)-X_u(\omega),
--   $$
--   where $X=\texttt{vectorItoProcess}(W,\mathcal F,H,X_0,b)$.
--
--   This map from $\Omega$ to $\mathrm{Fin}(n)\to\mathbb R$ is measurable.
--
--   The declaration is an auxiliary regularity lemma used to establish integrability of norms of vector-process increments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem measurable_vectorItoProcess_sub {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
--       Measurable fun ω => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
--         - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Previous: [`integral_abs_vectorItoMartingale_sub_le`](https://prove2.me/theorems/8b157a78-e3e6-4128-ac91-5b7ce7b8fb41) · Next: [`integral_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/8034fbf3-4cec-4cc1-8421-d12baf9f25de).
--
--   [Source excerpt, lines 380–382](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoProcess.lean#L380-L382) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoProcess.lean#L378-L395 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoProcess`, declaration `LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess_sub`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
include hbm hB

theorem LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess_sub_readable {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Measurable fun ω => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
      - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω := by sorry
