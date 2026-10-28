-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_clampMesh_mono_window_readable
-- name    : LevyStochCalc.Brownian.Ito.clampMesh_mono_window_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:39.90099+00:00
-- url     : https://prove2.me/theorems/17031eaf-0282-46a9-a32a-db61ccb38eec
-- title:
--   Monotonicity of the Clamping Mesh in the Window
-- statement:
--   This vendored theorem states that the clamping mesh is monotone in the time window.
--
--   Let $P$ be a measure on $\Omega$, let $H$ and $b$ be the coefficient families used to define `clampMesh`, and let $T\leq T'$ be real numbers. Then, for every $j\in\mathbb N$,
--
--   $$
--   \operatorname{clampMesh}(P,H,b,T,j)
--   \leq
--   \operatorname{clampMesh}(P,H,b,T',j).
--   $$
--
--   The result allows finite-energy estimates on larger time windows to control the corresponding mesh on smaller windows.
--
--   **Formalization Note.** The mesh is built from `ENNReal` integrals of squared coefficient-clamping errors; no finiteness assumption is present in the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem clampMesh_mono_window (P : Measure Ω) (H : Fin n → Fin d → Ω → ℝ → ℝ)
--       (b : Fin n → Ω → ℝ → ℝ) {T T' : ℝ} (hTT' : T ≤ T') (j : ℕ) :
--       clampMesh P H b T j ≤ clampMesh P H b T' j
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionLimit`](https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6).
--
--   Definition modules: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Previous: [`le_add_inv_mul_sq`](https://prove2.me/theorems/55fc83fc-8bfe-43c9-9ba2-4e5fb4a6199b) · Next: [`exists_seq_clampMesh_window_lt`](https://prove2.me/theorems/b2eb4ef5-6631-48e3-9006-913e761e4fc6).
--
--   [Source excerpt, lines 90–92](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L90-L92) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L89-L108 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionLimit`, declaration `LevyStochCalc.Brownian.Ito.clampMesh_mono_window`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}

theorem LevyStochCalc.Brownian.Ito.clampMesh_mono_window_readable (P : Measure Ω) (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) {T T' : ℝ} (hTT' : T ≤ T') (j : ℕ) :
    clampMesh P H b T j ≤ clampMesh P H b T' j := by sorry
