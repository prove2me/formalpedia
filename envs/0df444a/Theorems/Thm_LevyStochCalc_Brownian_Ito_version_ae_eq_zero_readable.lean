-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_version_ae_eq_zero_readable
-- name    : LevyStochCalc.Brownian.Ito.version_ae_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:42.843007+00:00
-- url     : https://prove2.me/theorems/ee3afebe-ae0f-4c3f-aa5d-fab65a71b613
-- title:
--   Initial Value of a Vector Itô Version
-- statement:
--   This vendored statement from LevyStochCalc asserts that a vector Itô version starts at its prescribed initial value.
--
--   Let $(\Omega,P)$ be a measurable probability space. Let $W$ be a $d$-dimensional Brownian motion under $P$, let $\mathcal F'$ be a filtration, and assume that every coordinate Brownian motion of $W$ is Brownian with respect to $\mathcal F'$. Let $H$, $X_0$, $b$, and $X$ satisfy the measurability, progressive measurability, local square-integrability, and vector-Itô-version hypotheses appearing in `IsVectorItoVersion`.
--
--   Then the process value at time zero equals the initial function almost everywhere:
--
--   $$
--   X(0)=X_0\quad\text{almost everywhere with respect to }P.
--   $$
--
--   The equality is an a.e. equality of functions $\Omega\to\operatorname{Fin}(n)\to\mathbb R$. This metadata describes the theorem from the vendored upstream repository at commit `984dbf0b790031eac05d56fe5a84b65e15e1e932`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem version_ae_eq_zero
--       {H : Fin n → Fin d → Ω → ℝ → ℝ}
--       {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
--       {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
--       {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
--       {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
--       (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X) :
--       X 0 =ᵐ[P] X₀
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Previous: [`ae_tendsto_version_clamp_at`](https://prove2.me/theorems/749d431d-d8f1-44b6-ba64-5d3e7974a377).
--
--   [Source excerpt, lines 520–528](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L520-L528) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L519-L553 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`, declaration `LevyStochCalc.Brownian.Ito.version_ae_eq_zero`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ')

theorem LevyStochCalc.Brownian.Ito.version_ae_eq_zero_readable
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X) :
    X 0 =ᵐ[P] X₀ := by sorry
