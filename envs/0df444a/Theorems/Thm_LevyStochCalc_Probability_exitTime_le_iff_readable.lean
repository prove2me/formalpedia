-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_readable
-- name    : LevyStochCalc.Probability.exitTime_le_iff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:31.997816+00:00
-- url     : https://prove2.me/theorems/ebd33cab-b36e-4b04-9cc1-92d3a27975cf
-- title:
--   Continuous-Path Exit-Time Characterization
-- statement:
--   This characterizes the exit time of a continuous path.
--
--   Let $E$ be a normed additive commutative group, let $X:\Omega\to\mathbb R\to E$, and fix $\omega\in\Omega$. Assume that the path $s\mapsto X(\omega,s)$ is continuous. For every level $k\in\mathbb R$ and time $t\in\mathbb R$,
--   $$
--   \operatorname{exitTime}(X,k,\omega)\le t
--   \iff
--   \exists s\in[0,t],\quad k\le\|X(\omega,s)\|.
--   $$
--
--   Thus the exit time is at most $t$ exactly when the path reaches norm at least $k$ at some point of the closed interval $[0,t]$.
--
--   This provides the basic deterministic criterion used to establish stopping-time and localization properties.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exitTime_le_iff {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k t : ℝ) :
--       exitTime X k ω ≤ (t : WithTop ℝ) ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖X ω s‖
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/ExitTime`](https://prove2.me/theorems/afef0596-dfb2-4d26-a303-b02e54dda356).
--
--   Next: [`abs_clamp_sub_le`](https://prove2.me/theorems/dd3d7b99-46be-440b-a1a2-c53a92717bb6).
--
--   [Source excerpt, lines 66–67](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/ExitTime.lean#L66-L67) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L64-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.exitTime_le_iff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

theorem LevyStochCalc.Probability.exitTime_le_iff_readable {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k t : ℝ) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖X ω s‖ := by sorry
