-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_prod_sub_one_eq_sum
-- name    : LevyStochCalc.Poisson.prod_sub_one_eq_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:55:59.309612+00:00
-- url     : https://prove2.me/theorems/64f9289c-b3ff-41a6-ab29-dac89107cb70
-- title:
--   prod sub one eq sum
-- statement:
--   The source theorem `LevyStochCalc.Poisson.prod_sub_one_eq_sum` is extracted from `LevyStochCalc.Poisson.ChainRule`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpSum_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump chain rule for a Poisson random measure

A product over a finite set whose factors are ordered by a key telescopes: the product minus one
is the sum, over the factors, of the product of the earlier ones times the increment of that
factor. On a set of finite reference intensity a Poisson random measure is a finite sum of unit
masses at distinct times, so the exponential of an integral against it obeys that telescoping,
which is the chain rule the exponential family needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

section Telescope

variable {α : Type*} [DecidableEq α] {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]

omit [DecidableEq α] in
open scoped Classical in

theorem _root_.LevyStochCalc.Poisson.prod_sub_one_eq_sum (key : α → K) (z : α → M) :
    ∀ s : Finset α, Set.InjOn key (s : Set α) →
      (∏ p ∈ s, z p) - 1
        = ∑ p ∈ s, (∏ q ∈ s.filter (fun q => key q < key p), z q) * (z p - 1) := by sorry
