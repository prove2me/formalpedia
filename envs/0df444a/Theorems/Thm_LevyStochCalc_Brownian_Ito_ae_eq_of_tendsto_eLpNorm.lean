-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_eq_of_tendsto_eLpNorm
-- name    : LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_eLpNorm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:30:38.057174+00:00
-- url     : https://prove2.me/theorems/32bb5760-f7df-4730-a310-bac9bc9a0db1
-- title:
--   ae eq of tendsto eLpNorm
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_eLpNorm` is extracted from `LevyStochCalc.Brownian.ItoDriverLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral in the driver

The elementary integral of a simple integrand against a linear combination of Brownian motions is
the corresponding combination of the elementary integrals, and both sides of the resulting
identity are `L²`-limits along the same approximating sequence, so the identity passes to the
`L²` Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_eLpNorm {f g : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) P)
    (hfm : AEStronglyMeasurable f P) (hgm : AEStronglyMeasurable g P)
    (hFf : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - f ω) 2 P) Filter.atTop (nhds 0))
    (hFg : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - g ω) 2 P) Filter.atTop (nhds 0)) :
    f =ᵐ[P] g := by sorry
