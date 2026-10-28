-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_abs_clamp_sub_le_readable
-- name    : LevyStochCalc.Probability.abs_clamp_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:32.112165+00:00
-- url     : https://prove2.me/theorems/dd3d7b99-46be-440b-a1a2-c53a92717bb6
-- title:
--   Clamping Does Not Increase Distance
-- statement:
--   This is an elementary estimate for projection onto a time interval.
--
--   Let $t\ge0$, let $s\in[0,t]$, and let $x\in\mathbb R$. Then clamping $x$ to $[0,t]$ does not increase its distance from $s$:
--   $$
--   \left|\max\{0,\min\{t,x\}\}-s\right|
--   \le |x-s|.
--   $$
--
--   The estimate is used to control time arguments after localization or truncation.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_clamp_sub_le {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (x : ℝ) :
--       |max 0 (min t x) - s| ≤ |x - s|
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/ExitTime`](https://prove2.me/theorems/afef0596-dfb2-4d26-a303-b02e54dda356).
--
--   Previous: [`exitTime_le_iff`](https://prove2.me/theorems/ebd33cab-b36e-4b04-9cc1-92d3a27975cf) · Next: [`exitTime_le_iff_forall`](https://prove2.me/theorems/71a39608-01e8-49d1-87e7-278e30c25025).
--
--   [Source excerpt, lines 87–88](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/ExitTime.lean#L87-L88) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L86-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.abs_clamp_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u v

theorem LevyStochCalc.Probability.abs_clamp_sub_le_readable {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (x : ℝ) :
    |max 0 (min t x) - s| ≤ |x - s| := by sorry
