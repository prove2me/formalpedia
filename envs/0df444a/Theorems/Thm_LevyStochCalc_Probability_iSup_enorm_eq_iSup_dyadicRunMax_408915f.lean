-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_iSup_enorm_eq_iSup_dyadicRunMax_408915f
-- name    : LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:59:19.957227+00:00
-- url     : https://prove2.me/theorems/0b821bd4-eebf-48ce-93a2-b29ec9377261
-- title:
--   Continuous Supremum from Dyadic Running Maxima
-- statement:
--   This vendored theorem identifies a continuous-time supremum with dyadic running maxima.
--
--   Let $T\geq0$, fix an outcome $\omega$, and suppose that the path $s\mapsto M_s(\omega)$ is right-continuous at every time. Then
--
--   $$
--   \sup_{t\in[0,T]}\|M_t(\omega)\|_{\mathrm{ENNReal}}
--   =
--   \sup_{n\in\mathbb N}
--   \|\operatorname{dyadicRunMax}(M,T,n,\omega)\|_{\mathrm{ENNReal}}.
--   $$
--
--   This is the pathwise bridge from discrete dyadic maximal estimates to a continuous-time supremum estimate.
--
--   **Formalization Note.** The supremum over $[0,T]$ is represented by an `iSup` over the subtype `Set.Icc 0 T`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/DoobContinuous.lean#L206-L241 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.DoobContinuous`, declaration `LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_408915f (hT : 0 ≤ T) {ω : Ω}
    (hcad : ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞))
      = ⨆ n, (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by sorry
