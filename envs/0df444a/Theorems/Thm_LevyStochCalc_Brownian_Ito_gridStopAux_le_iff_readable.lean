-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_gridStopAux_le_iff_readable
-- name    : LevyStochCalc.Brownian.Ito.gridStopAux_le_iff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:56.707986+00:00
-- url     : https://prove2.me/theorems/6f0d962f-df1d-4b16-a483-6c727c1385c0
-- title:
--   Grid Stopping Auxiliary Characterization
-- statement:
--   This is a technical equivalence characterizing the auxiliary grid stopping time `gridStopAux`.
--
--   Let Ω be a type, let τ : Ω → WithTop ℝ be an extended-real-valued stopping-time candidate, let t and a be real and extended-real parameters respectively, let n and k be natural numbers, and let ω : Ω. Then the following are equivalent: `gridStopAux τ t n k ω` is at most a, and there exists a natural number j such that j ≤ k and the two-valued stopping time `stepStop τ (gridPt t n j) ω` is at most a.
--
--   $$
--   \operatorname{gridStopAux}(\tau,t,n,k,\omega) \le a
--   \quad\Longleftrightarrow\quad
--   \exists j \le k,\; \operatorname{stepStop}(\tau,\operatorname{gridPt}(t,n,j),\omega) \le a.
--   $$
--
--   This auxiliary result rewrites an inequality involving the grid stopping time as a finite existential condition over grid indices, making it reusable in arguments about grid approximations and their order properties.
--
--   **Formalization Note**: The stopping-time values and the parameter a lie in `WithTop ℝ`, the extended real line, and all inequalities use its order. The statement has no measurability or probability-measure assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
--   theorem gridStopAux_le_iff (t : ℝ) (n k : ℕ) (ω : Ω) (a : WithTop ℝ) :
--       gridStopAux τ t n k ω ≤ a ↔ ∃ j ≤ k, stepStop τ (gridPt t n j) ω ≤ a
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoLocality`](https://prove2.me/theorems/24c85544-31a3-4ffd-a08e-f5b9ac9b8eba).
--
--   Next: [`eventually_gridStop_lt`](https://prove2.me/theorems/e741dfe5-2d5c-477d-97d6-46f4687f6103).
--
--   [Source excerpt, lines 99–101](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLocality.lean#L99-L101) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLocality.lean#L99-L122 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLocality`, declaration `LevyStochCalc.Brownian.Ito.gridStopAux_le_iff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)
omit [MeasurableSpace Ω] [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.gridStopAux_le_iff_readable (t : ℝ) (n k : ℕ) (ω : Ω) (a : WithTop ℝ) :
    gridStopAux τ t n k ω ≤ a ↔ ∃ j ≤ k, stepStop τ (gridPt t n j) ω ≤ a := by sorry
