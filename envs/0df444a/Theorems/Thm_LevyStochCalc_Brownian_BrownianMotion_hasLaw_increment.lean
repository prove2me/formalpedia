-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_increment
-- name    : LevyStochCalc.Brownian.BrownianMotion.hasLaw_increment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:27:57.189183+00:00
-- url     : https://prove2.me/theorems/d41dc272-08e4-4260-8a3d-35c00c577c18
-- title:
--   hasLaw increment
-- statement:
--   The source theorem `LevyStochCalc.Brownian.BrownianMotion.hasLaw_increment` is extracted from `LevyStochCalc.Brownian.MathlibBridge`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MathlibBridge_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian motion in the sense of Mathlib

A `BrownianMotion P` in the sense of `LevyStochCalc.Brownian.Construction`, restricted along the
coercion `ℝ≥0 → ℝ`, is a Brownian motion in the sense of `ProbabilityTheory.IsBrownianReal`: its
value at time `t` has law `gaussianReal 0 t`, its increments along a monotone tuple are mutually
independent, and its paths are almost surely continuous. Mutual independence of the increments
comes from the σ-algebra field `BrownianMotion.joint_increment_independent` through
`iIndep_of_indep_biSup_lt`, a chain criterion for mutual independence of a family of σ-algebras
indexed by a linear order.

## Main statements

* `iIndep_of_indep_biSup_lt` — a family of σ-algebras indexed by a linear order is mutually
  independent as soon as each member is independent of the supremum of its predecessors.
* `BrownianMotion.hasLaw_eval`, `BrownianMotion.hasLaw_increment` — the marginal laws.
* `BrownianMotion.hasIndepIncrements` — mutual independence of the increments.
* `BrownianMotion.isPreBrownianReal`, `BrownianMotion.isBrownianReal`,
  `BrownianMotion.isGaussianProcess` — the Mathlib predicates.
* `BrownianMotion.ofIsPreBrownianReal_w_ae_eq` — the round trip through
  `BrownianMotion.ofIsPreBrownianReal` recovers the paths at nonnegative times.
-/

namespace LevyStochCalc.Brownian

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace BrownianMotion

theorem _root_.LevyStochCalc.Brownian.BrownianMotion.hasLaw_increment (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (fun ω ↦ W.W (t : ℝ) ω - W.W (s : ℝ) ω) (gaussianReal 0 (t - s)) P := by sorry
