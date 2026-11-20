-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_exists
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:32:12.900009+00:00
-- url     : https://prove2.me/theorems/0cb994ed-7d93-4efa-9e19-0e521141f54f
-- title:
--   exists
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` is extracted from `LevyStochCalc.Brownian.Multidim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Multidim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# d-dimensional Brownian motion

A `d`-dimensional Brownian motion is a `Fin d`-tuple of independent 1-D
Brownian motions on the same probability space. Constructed on the finite
product `MeasureTheory.Measure.pi` of copies of a space carrying one, whose
coordinates are independent by `ProbabilityTheory.iIndepFun_pi`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.1.

## Contents

* `MultidimBrownianMotion` — the structure; `components_independent` is
  stated with `iIndepFun`, and `joint_continuous_paths` makes the almost-sure
  continuity of the vector-valued path explicit.
* `MultidimBrownianMotion.exists` — existence, via `MeasureTheory.Measure.pi` (finite
  product of probability spaces) and the independence of coordinate
  evaluations on a product measure; each coordinate is a 1-D Brownian motion
  lifted along the corresponding projection.
* `MultidimBrownianMotion.joint_increment_gaussian_diagonal` — each
  coordinate increment is Gaussian and the coordinate increments are
  independent.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim

universe u

section Definition
variable {Ω : Type u} [MeasurableSpace Ω]

end Definition

section MeasurePreserving
variable {Ω : Type u} [MeasurableSpace Ω]

end MeasurePreserving

section Existence
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists (d : ℕ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (MultidimBrownianMotion P d) := by sorry
