-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Martingale_brownian_martingale_natural
-- name    : LevyStochCalc.Brownian.Martingale.brownian_martingale_natural
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:23:46.919771+00:00
-- url     : https://prove2.me/theorems/2da676a7-36ef-4022-ba37-798d06c38dc5
-- title:
--   brownian martingale natural
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Martingale.brownian_martingale_natural` is extracted from `LevyStochCalc.Brownian.MartingaleQuadVar`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MartingaleQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian martingale property and quadratic variation

Brownian motion is a martingale for its natural filtration, hence for any filtration to which it
is adapted with independent increments, and its quadratic variation is `⟨W⟩_t = t`: the process
`W_t² − t` is again a martingale. The identity `(dW)² = dt` it records is the second-order term
of the Itô formula.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section MartingaleAndQuadVar
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Martingale.brownian_martingale_natural
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    MeasureTheory.Martingale (fun t : ℝ => W.W t) (naturalFiltration W) P := by sorry
