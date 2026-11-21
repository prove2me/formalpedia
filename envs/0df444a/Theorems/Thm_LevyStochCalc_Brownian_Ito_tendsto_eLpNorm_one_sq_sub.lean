-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_eLpNorm_one_sq_sub
-- name    : LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:36:29.199946+00:00
-- url     : https://prove2.me/theorems/1d6e768f-e8ae-4a62-a5b4-568f9fdaac77
-- title:
--   tendsto eLpNorm one sq sub
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionConvergence`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub
    {μ : MeasureTheory.Measure Ω} {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {b : Ω → ℝ}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
    (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
      l (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
      l (nhds 0) := by sorry
