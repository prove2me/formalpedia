-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_exists_lt_exitTime_408915f
-- name    : LevyStochCalc.Probability.exists_lt_exitTime_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:39:40.650534+00:00
-- url     : https://prove2.me/theorems/b8f09893-af26-4069-ad88-a0698bd8e0e8
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
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L215-L229 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.exists_lt_exitTime`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.exists_lt_exitTime_408915f {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (t : WithTop ℝ) < exitTime X (k : ℝ) ω := by sorry
