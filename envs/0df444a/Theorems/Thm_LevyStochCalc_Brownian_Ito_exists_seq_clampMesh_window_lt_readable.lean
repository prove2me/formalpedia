-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_seq_clampMesh_window_lt_readable
-- name    : LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:46.098904+00:00
-- url     : https://prove2.me/theorems/b2eb4ef5-6631-48e3-9006-913e761e4fc6
-- title:
--   Clamping Levels with Geometrically Small Mesh
-- statement:
--   This vendored existence theorem selects clamping levels whose mesh decays geometrically on every bounded window.
--
--   Let $P$ be a probability measure, let $H$ and $b$ be measurable coefficient families, and assume:
--
--   1. For every coefficient index and every $T>0$, the `ENNReal` energy of $H$ on $[0,T]$ is finite.
--   2. For every drift index and every $T>0$, the corresponding `ENNReal` energy of $b$ on $[0,T]$ is finite.
--
--   Then there exists a sequence $m_s:\mathbb N\to\mathbb N$ such that $s\leq m_s$ and, for every $s\in\mathbb N$,
--
--   $$
--   \operatorname{clampMesh}(P,H,b,s+1,m_s)
--   <
--   \left(\frac12\right)^{2s}
--   $$
--
--   in $[0,\infty]$.
--
--   This supplies clamping levels suitable for summability and convergence constructions on increasing windows.
--
--   **Formalization Note.** The mesh and the geometric bound are `ENNReal` values, and the strict inequality is in `ENNReal`.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_seq_clampMesh_window_lt {H : Fin n → Fin d → Ω → ℝ → ℝ}
--       (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
--       {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
--       (hq : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
--       ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
--         ∀ i : ℕ, clampMesh P H b ((i : ℝ) + 1) (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/VectorItoVersionLimit`](https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6).
--
--   Definition modules: [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb).
--
--   Supporting theorems: [`tendsto_energy_window_clamp`](https://prove2.me/theorems/cdd4a95d-5776-480a-ae2b-6a1001a8347e).
--
--   Previous: [`clampMesh_mono_window`](https://prove2.me/theorems/17031eaf-0282-46a9-a32a-db61ccb38eec) · Next: [`vectorItoProcess_ae_eq_zero`](https://prove2.me/theorems/2c299ed7-02cc-4215-b871-f99239baed20).
--
--   [Source excerpt, lines 124–132](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L124-L132) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/VectorItoVersionLimit.lean#L123-L146 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.VectorItoVersionLimit`, declaration `LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}

theorem LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt_readable {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hq : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
      ∀ i : ℕ, clampMesh P H b ((i : ℝ) + 1) (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by sorry
