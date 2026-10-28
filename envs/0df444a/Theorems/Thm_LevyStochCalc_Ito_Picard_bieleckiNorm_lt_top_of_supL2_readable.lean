-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_lt_top_of_supL2_readable
-- name    : LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:44.612986+00:00
-- url     : https://prove2.me/theorems/2df643b2-8d67-4af3-bd4c-c76523b1d9d8
-- title:
--   Finite $S^2$ Control Implies Finite Bielecki Norm
-- statement:
--   This shows that a finite windowwise $S^2$ bound gives a finite Bielecki norm at weight zero.
--
--   Let $P$ be a probability measure, let $T>0$, and let $Z:\mathbb R\to\Omega\to\mathbb R^n$. Assume that for every $T'>0$,
--
--   $$\int_\Omega\sup_{0\le t\le T'}\sum_{i<n}|Z(t,\omega,i)|^2\,dP(\omega)<\top.$$
--
--   Then
--
--   $$\operatorname{bieleckiNorm}(0,T,Z)<\top.$$
--
--   The supremum and integral are represented using `ENNReal`, and finiteness means strict inequality with $\top$. This provides the integrability input needed for Picard-space arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bieleckiNorm_lt_top_of_supL2 {T : ℝ} (hT : 0 < T) {Z : ℝ → Ω → (Fin n → ℝ)}
--       (hS : ∀ T' : ℝ, 0 < T' →
--         ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) :
--       bieleckiNorm (P := P) 0 T Z < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02).
--
--   Next: [`bieleckiNorm_sub_lt_top_of_lt_top`](https://prove2.me/theorems/02064a85-b521-4d2a-aa86-6273c40d71ff).
--
--   [Source excerpt, lines 84–87](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardWindow.lean#L84-L87) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardWindow.lean#L82-L103 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardWindow`, declaration `LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace E]

theorem LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2_readable {T : ℝ} (hT : 0 < T) {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) :
    bieleckiNorm (P := P) 0 T Z < ⊤ := by sorry
