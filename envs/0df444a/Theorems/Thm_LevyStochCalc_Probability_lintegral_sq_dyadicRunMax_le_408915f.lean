-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_lintegral_sq_dyadicRunMax_le_408915f
-- name    : LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:02:01.794037+00:00
-- url     : https://prove2.me/theorems/b03134a1-598a-4bd7-8c27-f2f330e28f2e
-- title:
--   Dyadic $L^2$ Maximal Bound for a Martingale
-- statement:
--   This is a dyadic $L^2$ maximal inequality for a continuous-time martingale sampled at dyadic times.
--
--   Let $(\Omega,\mathcal F,P)$ be a finite probability space, let $M:\mathbb R\to\Omega\to\mathbb R$ be a martingale relative to a filtration $\mathcal F$, and let $T\ge0$. For every $n\in\mathbb N$, let `dyadicRunMax M T n` be the running maximum along the dyadic partition of $[0,T]$ at level $n$.
--
--   $$\int_\Omega \bigl\|\operatorname{dyadicRunMax}(M,T,n)(\omega)\bigr\|^2\,dP(\omega)\le 4\int_\Omega |M_T(\omega)|^2\,dP(\omega).$$
--
--   The integrals are `ENNReal` lower integrals, and the norm is represented by the nonnegative norm coercion. The estimate is intended for dyadic maximal-control arguments.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L267-L291 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le_408915f {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) (n : ℕ) :
    ∫⁻ ω, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by sorry
