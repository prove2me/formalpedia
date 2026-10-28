-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_sub_lt_top_of_lt_top_readable
-- name    : LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top_of_lt_top_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:50.839679+00:00
-- url     : https://prove2.me/theorems/02064a85-b521-4d2a-aa86-6273c40d71ff
-- title:
--   Finite Bielecki Norm of a Difference
-- statement:
--   This proves finiteness of the Bielecki norm of a difference from finiteness of the two component norms.
--
--   Let $P$ be a probability measure, let $\beta\ge0$, let $T\in\mathbb R$, and let $X,Y:\mathbb R\to\Omega\to\mathbb R^n$ be jointly measurable. Assume
--
--   $$\operatorname{bieleckiNorm}(0,T,X)<\top,\qquad \operatorname{bieleckiNorm}(0,T,Y)<\top.$$
--
--   Then
--
--   $$\operatorname{bieleckiNorm}\bigl(\beta,T,(t,\omega,i)\mapsto X(t,\omega,i)-Y(t,\omega,i)\bigr)<\top.$$
--
--   The conclusion concerns the `ENNReal`-valued Bielecki norm and holds for every nonnegative weight $\beta$. It is a basic closure property of the Picard space.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bieleckiNorm_sub_lt_top_of_lt_top {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
--       {X Y : ℝ → Ω → (Fin n → ℝ)}
--       (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
--       (hX : bieleckiNorm (P := P) 0 T X < ⊤) (hY : bieleckiNorm (P := P) 0 T Y < ⊤) :
--       bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) < ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f).
--
--   Definition modules: [`LevyStochCalc/Ito/PicardBieleckiNorm`](https://prove2.me/theorems/7e1224ac-a352-46d7-9a7e-a9c4b7a20a02).
--
--   Previous: [`bieleckiNorm_lt_top_of_supL2`](https://prove2.me/theorems/2df643b2-8d67-4af3-bd4c-c76523b1d9d8) · Next: [`ae_eq_of_solvesOn`](https://prove2.me/theorems/68acae9c-cef9-4b55-9b63-0571ce263cb6).
--
--   [Source excerpt, lines 107–111](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardWindow.lean#L107-L111) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardWindow.lean#L105-L131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardWindow`, declaration `LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top_of_lt_top`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace E]

theorem LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top_of_lt_top_readable {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    {X Y : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X)) (hYm : Measurable (Function.uncurry Y))
    (hX : bieleckiNorm (P := P) 0 T X < ⊤) (hY : bieleckiNorm (P := P) 0 T Y < ⊤) :
    bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) < ⊤ := by sorry
