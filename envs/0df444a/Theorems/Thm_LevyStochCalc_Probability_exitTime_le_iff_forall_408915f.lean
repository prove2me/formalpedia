-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_forall_408915f
-- name    : LevyStochCalc.Probability.exitTime_le_iff_forall_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:39:41.536641+00:00
-- url     : https://prove2.me/theorems/71aed234-0026-4b23-9e1c-86742d7d395b
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
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L110-L141 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.exitTime_le_iff_forall`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.exitTime_le_iff_forall_408915f {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔
      ∀ n : ℕ, ∃ m : ℕ, k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖ := by sorry
