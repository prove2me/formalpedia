-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_408915f
-- name    : LevyStochCalc.Probability.exitTime_le_iff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:39:45.115858+00:00
-- url     : https://prove2.me/theorems/6f9f9922-e806-4108-828f-a72c9a8bc208
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
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L64-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.exitTime_le_iff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.exitTime_le_iff_408915f {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k t : ℝ) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖X ω s‖ := by sorry
