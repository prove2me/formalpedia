-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_norm_clampProcess_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_sq_norm_clampProcess_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:32.612878+00:00
-- url     : https://prove2.me/theorems/3cedae93-25d4-48aa-8734-4c7f786afa37
-- title:
--   L² Error for Clamped Itô Processes
-- statement:
--   Let W, ℱ, H, X₀, and b satisfy the measurability, progressive measurability, and finite `ENNReal` square-energy hypotheses in the declaration. For a truncation level j : ℕ, use `clampCoeff H j` and `clampDrift b j` to form the clamped process, and let 0 < t ≤ T. Then the squared `ENNReal` L² distance between the clamped and original `vectorItoProcess` at time t is bounded by `clampMesh P H b T j`:
--
--   $$\int^\infty\|X^{\mathrm{clamp},j}_t-X_t\|_+^2\,dP\le\operatorname{clampMesh}(P,H,b,T,j).$$
--
--   The bound is uniform for times in the window [0,T] through the use of the mesh at T.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_sq_norm_clampProcess_sub_le
--       {H : Fin n → Fin d → Ω → ℝ → ℝ}
--       (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
--       (hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k))
--       (hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
--       {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
--       (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (j : ℕ) {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
--       ∫⁻ ω, (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
--               (fun p k => measurable_clampCoeff hm j p k)
--               (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
--               (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
--               X₀ (clampDrift b j) t ω
--           - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
--         ≤ clampMesh P H b T j
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Supporting theorems: [`lintegral_sq_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/868b1ad2-f913-46c1-9da7-a8c67dc44c11).
--
--   Previous: [`tendsto_energy_window_clamp`](https://prove2.me/theorems/cdd4a95d-5776-480a-ae2b-6a1001a8347e) · Next: [`lintegral_sq_norm_version_clamp_sub_le`](https://prove2.me/theorems/6384e99c-cf6e-4a54-9bca-3a969c3bbe48).
--
--   [Source excerpt, lines 156–173](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L156-L173) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean#L154-L196 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedClamp`, declaration `LevyStochCalc.Brownian.Ito.lintegral_sq_norm_clampProcess_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.lintegral_sq_norm_clampProcess_sub_le_readable
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (j : ℕ) {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫⁻ ω, (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
            X₀ (clampDrift b j) t ω
        - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ clampMesh P H b T j := by sorry
