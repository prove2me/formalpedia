-- Prove2me | Theorems.Thm_MarkovProcess_Measure_eq_of_map_finiteRestriction_eq
-- name    : MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:13:42.993783+00:00
-- url     : https://prove2.me/theorems/c93f52f8-7a51-49ec-996c-69c80445757f
-- title:
--   Finite-coordinate marginal uniqueness for finite measures
-- statement:
--   Let $\mu$ and $\nu$ be measures on a product measurable space, and suppose $\mu$ is finite. If for every finite set of coordinates $I$ the pushforward measures under coordinate restriction agree, then $\mu=\nu$. The empty coordinate set is included, so the marginal equations also determine total mass. Source-faithful formalisation from Scott Armstrong, MarkovProcess (Apache-2.0).
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/MeasureFiniteRestrictionIdentification.lean#L28-L44

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Constructions.Projective
open MeasureTheory
variable {index alpha : Type*} [MeasurableSpace alpha]

theorem MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
    (mu nu : Measure (index → alpha)) [IsFiniteMeasure mu]
    (h : ∀ I : Finset index, mu.map I.restrict = nu.map I.restrict) :
    mu = nu := by sorry
