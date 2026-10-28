-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exists_lt_exitTime_readable
-- name    : LevyStochCalc.Probability.exists_lt_exitTime_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:29.979984+00:00
-- url     : https://prove2.me/theorems/49d175b4-5189-43f1-894f-62a131c2b9d1
-- title:
--   Eventual Exit-Time Localization
-- statement:
--   This is the localization property for continuous paths.
--
--   Let $E$ be a normed additive commutative group, let $X:\Omega\to\mathbb R\to E$, and assume that $s\mapsto X(\omega,s)$ is continuous. For every $t\ge0$, there exists a natural number $K$ such that every integer $k\ge K$ satisfies
--   $$
--    t<\operatorname{exitTime}(X,k,\omega).
--   $$
--
--   Equivalently, any fixed nonnegative time lies strictly before all sufficiently high exit levels. The result supplies a localizing sequence for continuous paths.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_lt_exitTime {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {t : ℝ} (ht : 0 ≤ t) :
--       ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (t : WithTop ℝ) < exitTime X (k : ℝ) ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Probability/ExitTime`](https://prove2.me/theorems/afef0596-dfb2-4d26-a303-b02e54dda356).
--
--   Supporting theorems: [`exitTime_le_iff`](https://prove2.me/theorems/ebd33cab-b36e-4b04-9cc1-92d3a27975cf).
--
--   Previous: [`norm_le_of_le_exitTime`](https://prove2.me/theorems/657fcfbb-b024-4d35-9d2d-20d9b2769cee).
--
--   [Source excerpt, lines 217–218](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/ExitTime.lean#L217-L218) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L215-L229 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.exists_lt_exitTime`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

theorem LevyStochCalc.Probability.exists_lt_exitTime_readable {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (t : WithTop ℝ) < exitTime X (k : ℝ) ω := by sorry
