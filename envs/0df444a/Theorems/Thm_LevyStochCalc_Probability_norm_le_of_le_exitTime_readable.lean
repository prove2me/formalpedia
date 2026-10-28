-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_norm_le_of_le_exitTime_readable
-- name    : LevyStochCalc.Probability.norm_le_of_le_exitTime_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:30.496778+00:00
-- url     : https://prove2.me/theorems/657fcfbb-b024-4d35-9d2d-20d9b2769cee
-- title:
--   Norm Bound Before a Continuous-Path Exit Time
-- statement:
--   This bounds a continuous path before its exit time.
--
--   Let $E$ be a normed additive commutative group, let $X:\Omega\to\mathbb R\to E$ have a continuous path at $\omega$, and let $s>0$. If
--   $$
--    s\le\operatorname{exitTime}(X,k,\omega),
--   $$
--   then
--   $$
--   \|X(\omega,s)\|\le k.
--   $$
--
--   The restriction $s>0$ is part of the statement. The lemma is used to obtain uniform bounds on paths before localization.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_le_of_le_exitTime {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
--       (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ exitTime X k ω) : ‖X ω s‖ ≤ k
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/ExitTime`](https://prove2.me/theorems/afef0596-dfb2-4d26-a303-b02e54dda356).
--
--   Previous: [`exitTime_le_iff_forall`](https://prove2.me/theorems/71a39608-01e8-49d1-87e7-278e30c25025) · Next: [`exists_lt_exitTime`](https://prove2.me/theorems/49d175b4-5189-43f1-894f-62a131c2b9d1).
--
--   [Source excerpt, lines 194–195](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/ExitTime.lean#L194-L195) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L191-L213 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.norm_le_of_le_exitTime`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

theorem LevyStochCalc.Probability.norm_le_of_le_exitTime_readable {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
    (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ exitTime X k ω) : ‖X ω s‖ ≤ k := by sorry
