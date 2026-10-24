-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_abs_clamp_sub_le_408915f
-- name    : LevyStochCalc.Probability.abs_clamp_sub_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:39:39.576064+00:00
-- url     : https://prove2.me/theorems/014ad6ce-ee1e-4642-af3b-2b3e36dc7030
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
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L86-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.abs_clamp_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
import Mathlib.Data.Rat.Denumerable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

theorem LevyStochCalc.Probability.abs_clamp_sub_le_408915f {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (x : ℝ) :
    |max 0 (min t x) - s| ≤ |x - s| := by sorry
