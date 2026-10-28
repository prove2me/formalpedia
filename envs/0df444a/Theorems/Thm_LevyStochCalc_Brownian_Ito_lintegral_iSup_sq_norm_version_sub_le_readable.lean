-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_iSup_sq_norm_version_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:21.463987+00:00
-- url     : https://prove2.me/theorems/3d71b361-cb18-4a6b-a812-4786fccd9817
-- title:
--   Window Supremum Bound for Two Vector Itô Versions
-- statement:
--   This bounds the second moment of the window supremum of the difference between two vector Itô versions.
--
--   Let $P$ be a probability measure, let $W$ be a $d$-dimensional Brownian motion with filtration $\mathcal F$, and suppose each Brownian coordinate induces a Brownian filtration. Let $X,Y:\mathbb R\to\Omega\to\mathbb R^n$ be vector Itô versions with common initial value $X_0$, drifts $b_1,b_2$, and diffusion coefficients $H_1,H_2$. Assume the coefficient functions are measurable and progressively measurable, and that their squared energies on every interval $[0,T]$, for $T>0$, are strictly below $\top$ in `ENNReal`.
--
--   For every $T>0$,
--
--   $$\int_\Omega\sup_{0\le t\le T}\|Y_t-X_t\|^2\,dP\le n^2\sum_{p<n}\left[4\,\operatorname{ofReal}(T)\int_\Omega\int_0^T\|b_{2,p}-b_{1,p}\|^2\,ds\,dP+16d\sum_{k<d}\int_\Omega\int_0^T\|H_{2,pk}-H_{1,pk}\|^2\,ds\,dP\right].$$
--
--   The supremum is represented as an `ENNReal` iSup over $[0,T]$, and all energy finiteness assumptions are strict inequalities below $\top$. This is a technical stability estimate for vector Itô versions.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {X Y : ℝ → Ω → Fin n → ℝ}
--       (hX : IsVectorItoVersion W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ X)
--       (hY : IsVectorItoVersion W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ Y)
--       {T : ℝ} (hT : 0 < T) :
--       ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
--         ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
--             (4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--                 (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
--               + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--                 (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionSup`](https://prove2.me/theorems/eac19afb-1a3e-420c-b0c9-4e8c576afefc).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Selected supporting theorems: [`lintegral_energy_lt_top_of_bound`](https://prove2.me/theorems/16b799ee-a736-423f-b93d-da4952047315), [`martingale_finsetSum`](https://prove2.me/theorems/fba98d15-9105-40a1-9195-5076f35b1f94), [`sq_enorm_finsetSum_le`](https://prove2.me/theorems/cf9da524-3235-4f23-9dbe-288975948e0e), [`enorm_dyadicRunMax`](https://prove2.me/theorems/df28b675-5880-4511-8fdc-de21a750c0cb), [`iSup_enorm_eq_iSup_dyadicRunMax`](https://prove2.me/theorems/acb0a4f1-b242-45cd-80de-139b129bb826).
--
--   Previous: [`martingale_finsetSum`](https://prove2.me/theorems/fba98d15-9105-40a1-9195-5076f35b1f94) · Next: [`lintegral_energy_sub_le`](https://prove2.me/theorems/b2a75191-454e-466b-aa72-6635b7bb48fd).
--
--   [Source excerpt, lines 147–158](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionSup.lean#L147-L158) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionSup.lean#L128-L373 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionSup`, declaration `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionSup

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionSup.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
include hcoord

theorem LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le_readable
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k))}
    {hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k)}
    {hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k))}
    {hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k)}
    {hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X Y : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ X)
    (hY : IsVectorItoVersion W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ Y)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
          (4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) := by sorry
