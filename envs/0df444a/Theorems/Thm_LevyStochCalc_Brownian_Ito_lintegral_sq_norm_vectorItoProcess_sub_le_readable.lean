-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_norm_vectorItoProcess_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:19.867555+00:00
-- url     : https://prove2.me/theorems/868b1ad2-f913-46c1-9da7-a8c67dc44c11
-- title:
--   L² Distance Between Vector Itô Processes
-- statement:
--   Let (Ω, P) be a probability space with a d-dimensional Brownian motion W and filtration ℱ. Consider two vector Itô processes driven by the same measurable, progressively measurable diffusion framework H₁ and H₂ and the same measurable initial value X₀, but with drifts b₁ and b₂. Assume all four coefficient families satisfy the stated finite `ENNReal` square-energy conditions, and assume t > 0. Then
--
--   $$\int^\infty\!\left(\|X^{(2)}_t-X^{(1)}_t\|_+\!:\!\mathbb{R}_{\ge0\infty}\right)^2dP\le\sum_{p<n}\left[2\,t\int^\infty\!\int_{[0,t]}\|b_{2,p}-b_{1,p}\|_+^2\,ds\,dP+2d\sum_{k<d}\int^\infty\!\int_{[0,t]}\|H_{2,pk}-H_{1,pk}\|_+^2\,ds\,dP\right].$$
--
--   Here the left-hand integral is the `ENNReal` integral of the squared extended norm, and the displayed notation `∫^∞` denotes the corresponding `lintegral`. This estimate separates drift and diffusion errors and is used for stability of vector Itô processes.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_norm_vectorItoProcess_sub_le
--       {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
--       (hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k)))
--       (hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k))
--       (hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k)))
--       (hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k))
--       (hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
--       {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
--       (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
--       (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
--       {t : ℝ} (ht : 0 < t)
--       (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
--       ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
--           - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
--         ≤ ∑ p : Fin n, (2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
--               (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--             + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
--               (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoProcessDiff`](https://prove2.me/theorems/cd1eb156-9d40-4d90-80b1-58b54714509a).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Supporting theorems: [`lintegral_energy_lt_top_of_bound`](https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315), [`sq_enorm_finsetSum_le`](https://prove2.me/theorems/cf9da524-3235-4f23-9dbe-288975948e0e).
--
--   [Source excerpt, lines 54–78](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoProcessDiff.lean#L54-L78) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoProcessDiff.lean#L53-L190 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoProcessDiff`, declaration `LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoProcessDiff

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoProcessDiff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)

theorem LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le_readable
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k)))
    (hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k))
    (hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k)))
    (hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k))
    (hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    {t : ℝ} (ht : 0 < t)
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖vectorItoProcess W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ t ω
        - vectorItoProcess W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ p : Fin n, (2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by sorry
