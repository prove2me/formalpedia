-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_countable_setOf_pos_ne_of_cadlag
-- name    : LevyStochCalc.Ito.countable_setOf_pos_ne_of_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:01:10.289222+00:00
-- url     : https://prove2.me/theorems/3cf2f941-279d-45e4-8131-d39afc4dcf53
-- title:
--   countable setOf pos ne of cadlag
-- statement:
--   The source theorem `LevyStochCalc.Ito.countable_setOf_pos_ne_of_cadlag` is extracted from `LevyStochCalc.Ito.JumpIntegrandLeftLim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpIntegrandLeftLim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands evaluated along the left limits of a path

A path in `ℝⁿ` that is right continuous on `[0, ∞)` and has left limits at every positive time
meets those left limits off a countable, hence Lebesgue null, set of times. An integrand
evaluated along such a path and the same integrand evaluated along a process that meets the path
at all but countably many positive times therefore agree almost everywhere for the product of the
sample measure, Lebesgue measure on the horizon and the mark measure, so the compensated integral
takes the same value on the two integrands; the same null set serves the iterated integral
against the mark measure and Lebesgue measure and the integral against the reference intensity.

The identification is one of `L²` classes: it concerns the compensated integral constructed from
the energy isometry, not a pathwise Stieltjes integral against the jump measure, for which the
two conventions differ.

## Main statements

* `countable_setOf_pos_ne_of_cadlag` — a path right continuous on `[0, ∞)` differs from its left
  limits at only countably many positive times.
* `compensatedIntegral_congr_of_countable_ne` — the compensated integrals of an integrand
  evaluated along two processes meeting at all but countably many positive times agree almost
  surely.
* `setIntegral_congr_of_countable_ne` and
  `setIntegral_referenceIntensity_congr_of_countable_ne` — the same for the compensator drift
  term, in its iterated and its product-measure form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito

universe u v w

section Cadlag

variable {n : ℕ}

theorem _root_.LevyStochCalc.Ito.countable_setOf_pos_ne_of_cadlag {f g : ℝ → Fin n → ℝ}
    (hright : ∀ t : ℝ, 0 ≤ t → Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      Tendsto (fun s => f s i) (𝓝[<] t) (𝓝 (g t i))) :
    {t : ℝ | 0 < t ∧ f t ≠ g t}.Countable := by sorry
