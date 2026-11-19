-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_isPiSystem_finInters
-- name    : LevyStochCalc.Probability.isPiSystem_finInters
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:27:47.255058+00:00
-- url     : https://prove2.me/theorems/02b0e07b-05ba-46dd-9dcc-2d3e7c57f970
-- title:
--   isPiSystem finInters
-- statement:
--   The source theorem `LevyStochCalc.Probability.isPiSystem_finInters` is extracted from `LevyStochCalc.Probability.IntegerValuedMeasure`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_IntegerValuedMeasure_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integer-valued finite measures

A measure is integer-valued when every measurable set carries a natural mass. On a measurable
space with a countable separating family such a measure, if finite, is a finite sum of Dirac
masses: a binary search along the separating family isolates a point of mass at least one, and
removing it lowers the total mass by at least one, so the recursion terminates.

Integrality on a generating π-system already gives integrality everywhere, since the sets of
natural mass form a Dynkin system as soon as the ambient measure is finite.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

section PiSystem

omit [MeasurableSpace α] in
theorem _root_.LevyStochCalc.Probability.isPiSystem_finInters (s : ℕ → Set α) : IsPiSystem (finInters s) := by sorry
