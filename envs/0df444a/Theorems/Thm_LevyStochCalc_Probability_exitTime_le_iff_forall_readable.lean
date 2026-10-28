-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_forall_readable
-- name    : LevyStochCalc.Probability.exitTime_le_iff_forall_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:27.498177+00:00
-- url     : https://prove2.me/theorems/71a39608-01e8-49d1-87e7-278e30c25025
-- title:
--   Exit Time Detected on Rational Grid Points
-- statement:
--   This characterizes a continuous-path exit event using the grid points `gridPt`.
--
--   Let $E$ be a normed additive commutative group, let $X:\Omega\to\mathbb R\to E$, and assume that $s\mapsto X(\omega,s)$ is continuous. Fix $k\in\mathbb R$ and $t\ge0$. Then
--   $$
--   \operatorname{exitTime}(X,k,\omega)\le t
--   \iff
--   \forall n\in\mathbb N,\ \exists m\in\mathbb N,
--   \quad k-\frac1{n+1}<\|X(\omega,\operatorname{gridPt}(t,m))\|.
--   $$
--
--   The comparison with the exit time is therefore determined by values of the path at grid points in $[0,t]$, with arbitrarily small loss in the threshold. This form is useful for measurability and stopping-time arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exitTime_le_iff_forall {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) {t : ℝ}
--       (ht : 0 ≤ t) :
--       exitTime X k ω ≤ (t : WithTop ℝ) ↔
--         ∀ n : ℕ, ∃ m : ℕ, k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/ExitTime`](https://prove2.me/theorems/afef0596-dfb2-4d26-a303-b02e54dda356).
--
--   Supporting theorems: [`abs_clamp_sub_le`](https://prove2.me/theorems/dd3d7b99-46be-440b-a1a2-c53a92717bb6), [`exitTime_le_iff`](https://prove2.me/theorems/ebd33cab-b36e-4b04-9cc1-92d3a27975cf).
--
--   Previous: [`abs_clamp_sub_le`](https://prove2.me/theorems/dd3d7b99-46be-440b-a1a2-c53a92717bb6) · Next: [`norm_le_of_le_exitTime`](https://prove2.me/theorems/657fcfbb-b024-4d35-9d2d-20d9b2769cee).
--
--   [Source excerpt, lines 112–115](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/ExitTime.lean#L112-L115) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L110-L141 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.exitTime_le_iff_forall`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

theorem LevyStochCalc.Probability.exitTime_le_iff_forall_readable {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔
      ∀ n : ℕ, ∃ m : ℕ, k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖ := by sorry
