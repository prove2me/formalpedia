-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_SecondMoment_integral_add_mul_add
-- name    : LevyStochCalc.Ito.SecondMoment.integral_add_mul_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:22:06.926414+00:00
-- url     : https://prove2.me/theorems/cd8a99d3-d89e-4dc4-98b7-eeeb31301f0d
-- title:
--   integral add mul add
-- statement:
--   The source theorem `LevyStochCalc.Ito.SecondMoment.integral_add_mul_add` is extracted from `LevyStochCalc.Ito.SecondMomentToolkit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Ito.SecondMoment.integral_add_mul_add {a b c d : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P)
    (hc : MemLp c 2 P) (hd : MemLp d 2 P) :
    ∫ ω, (a ω + b ω) * (c ω + d ω) ∂P
      = ∫ ω, a ω * c ω ∂P + ∫ ω, a ω * d ω ∂P + ∫ ω, b ω * c ω ∂P + ∫ ω, b ω * d ω ∂P := by sorry
