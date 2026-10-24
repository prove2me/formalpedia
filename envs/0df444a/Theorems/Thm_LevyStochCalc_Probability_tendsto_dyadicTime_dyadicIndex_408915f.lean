-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_tendsto_dyadicTime_dyadicIndex_408915f
-- name    : LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:11.223759+00:00
-- url     : https://prove2.me/theorems/230b04a9-0432-483b-a4b8-de128c305eb8
-- title:
--   Rightward Convergence of Dyadic Sampling Points
-- statement:
--   This vendored convergence theorem concerns dyadic sampling of a time point.
--
--   Let $T>0$ and let $t\in[0,T]$. For each $n$, let `dyadicIndex T t n` select the dyadic point at level $n$ lying at or to the right of $t$. Then
--
--   $$
--   \operatorname{dyadicTime}(T,n,\operatorname{dyadicIndex}(T,t,n))
--   \longrightarrow t
--   $$
--
--   as $n\to\infty$, with convergence in the neighborhood filter of $t$ restricted to $[t,\infty)$.
--
--   The result supplies the time approximation needed to pass from dyadic samples to right-continuous paths.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L186-L204 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}

theorem LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex_408915f {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (htT : t ≤ T) :
    Filter.Tendsto (fun n => dyadicTime T n (dyadicIndex T t n)) Filter.atTop
      (nhdsWithin t (Set.Ici t)) := by sorry
