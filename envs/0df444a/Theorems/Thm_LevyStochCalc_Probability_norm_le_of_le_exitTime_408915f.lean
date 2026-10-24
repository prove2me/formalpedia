-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_norm_le_of_le_exitTime_408915f
-- name    : LevyStochCalc.Probability.norm_le_of_le_exitTime_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:39:43.341982+00:00
-- url     : https://prove2.me/theorems/0b49d3ce-3960-4554-9c2e-a24ea942c4fc
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
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L191-L213 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, declaration `LevyStochCalc.Probability.norm_le_of_le_exitTime`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.norm_le_of_le_exitTime_408915f {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
    (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ exitTime X k ω) : ‖X ω s‖ ≤ k := by sorry
