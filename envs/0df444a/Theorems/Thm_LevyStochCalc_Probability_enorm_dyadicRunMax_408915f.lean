-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_408915f
-- name    : LevyStochCalc.Probability.enorm_dyadicRunMax_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:20.710333+00:00
-- url     : https://prove2.me/theorems/965eb036-be6c-486a-968d-ff9f089bd501
-- title:
--   Extended Norm of the Dyadic Running Maximum
-- statement:
--   This vendored theorem identifies the extended norm of a sampled running maximum.
--
--   For a real-valued process $M_t(\omega)$, a horizon $T$, a level $n\in\mathbb N$, and an outcome $\omega$, the `ENNReal` norm of `dyadicRunMax M T n ω` equals the supremum over the $2^n+1$ dyadic partition points:
--
--   $$
--   \|\operatorname{dyadicRunMax}(M,T,n,\omega)\|_{\mathrm{ENNReal}}
--   =
--   \sup_{k\in\operatorname{Fin}(2^n+1)}
--   \|M_{\operatorname{dyadicTime}(T,n,k)}(\omega)\|_{\mathrm{ENNReal}}.
--   $$
--
--   This provides the discrete supremum representation used in continuous-time maximal estimates.
--
--   **Formalization Note.** The supremum is an `ENNReal` supremum of the coerced nonnegative norms.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L109-L128 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.enorm_dyadicRunMax`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.enorm_dyadicRunMax_408915f (M : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (ω : Ω) :
    (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞)
      = ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) := by sorry
