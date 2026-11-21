-- Prove2me | Theorems.Thm_LevyStochCalc_Driver_LevyDriver_isPoissonFiltration
-- name    : LevyStochCalc.Driver.LevyDriver.isPoissonFiltration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T07:16:24.543018+00:00
-- url     : https://prove2.me/theorems/2a582f46-a9b9-4100-813f-fa7feff5a6a2
-- title:
--   isPoissonFiltration
-- statement:
--   The source theorem `LevyStochCalc.Driver.LevyDriver.isPoissonFiltration` is extracted from `LevyStochCalc.Driver.Joint`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint filtration of an independent Brownian motion and Poisson random measure

A `LevyDriver` is a `d`-dimensional Brownian motion `W` and a Poisson random measure `N` on one
probability space, with `σ(W)` independent of `σ(N)`. Its joint natural filtration
`(⨆ i, ℱ^{Wⁱ}) ⊔ ℱ^N` is one for which every coordinate `Wⁱ` is a Brownian motion and `N` a
Poisson random measure (`LevyDriver.isBrownianFiltration`, `LevyDriver.isPoissonFiltration`):
the increments of `Wⁱ` after `s` are independent of `ℱ^{Wⁱ} s`, and the rest of the joint
filtration at time `s` is independent of `σ(Wⁱ)` altogether, so the join stays independent
(`indep_sup_left_of_indep`); likewise for the future counts of `N`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

theorem _root_.LevyStochCalc.Driver.LevyDriver.isPoissonFiltration : Poisson.IsPoissonFiltration D.N D.filtration := by sorry
