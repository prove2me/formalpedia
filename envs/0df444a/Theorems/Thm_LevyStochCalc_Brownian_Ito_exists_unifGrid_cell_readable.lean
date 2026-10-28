-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_unifGrid_cell_readable
-- name    : LevyStochCalc.Brownian.Ito.exists_unifGrid_cell_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:59.782769+00:00
-- url     : https://prove2.me/theorems/6498e1ec-297e-4445-a8b4-20374c8bb9d6
-- title:
--   Existence of a Uniform-Grid Cell
-- statement:
--   This is a technical fact about the uniform time grid.
--
--   Let $T,s\in\mathbb R$ and $m\in\mathbb N$ satisfy $0<T$, $m\ne0$, $0<s$, and $s\le T$. For the grid point
--   $$
--   t_i=\operatorname{unifGrid}(T,m,i),
--   $$
--   there exists an index $i\in\mathbb N$ such that
--   $$
--   i<m,\qquad t_i<s,\qquad s\le t_{i+1}.
--   $$
--
--   Thus every time in $(0,T]$ lies in one of the half-open cells of the uniform partition.
--
--   This lemma is reused to locate time points in grid-based arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_unifGrid_cell {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {s : ℝ}
--       (hs : 0 < s) (hsT : s ≤ T) :
--       ∃ i : ℕ, i < m ∧ unifGrid T m i < s ∧ s ≤ unifGrid T m (i + 1)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f).
--
--   Next: [`integral_abs_add_pow_three_le`](https://prove2.me/theorems/4a99bb18-8c7c-4d98-a0f3-3e51e759119b).
--
--   [Source excerpt, lines 81–83](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFormulaGrid.lean#L81-L83) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFormulaGrid.lean#L80-L111 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFormulaGrid`, declaration `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u

theorem LevyStochCalc.Brownian.Ito.exists_unifGrid_cell_readable {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {s : ℝ}
    (hs : 0 < s) (hsT : s ≤ T) :
    ∃ i : ℕ, i < m ∧ unifGrid T m i < s ∧ s ≤ unifGrid T m (i + 1) := by sorry
