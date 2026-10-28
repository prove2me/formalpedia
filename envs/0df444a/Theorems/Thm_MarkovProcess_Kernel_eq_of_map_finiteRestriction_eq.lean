-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_eq_of_map_finiteRestriction_eq
-- name    : MarkovProcess.Kernel.eq_of_map_finiteRestriction_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:13:32.600594+00:00
-- url     : https://prove2.me/theorems/3b1ed27e-72f1-4b0e-9d94-d4c4bbe602b9
-- title:
--   Finite-coordinate marginal uniqueness for finite kernels
-- statement:
--   Let $\kappa$ and $\eta$ be kernels from a measurable parameter space to a countable or arbitrary product measurable space, with $\kappa$ a finite kernel. Equality of all finite-coordinate pushforward kernels implies equality of the original kernels. This holds pointwise by uniqueness of finite projective limits. Source-faithful formalisation from Scott Armstrong, MarkovProcess (Apache-2.0).
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/FiniteRestrictionIdentification.lean#L28-L47

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Kernel.Composition.MapComap
open MeasureTheory ProbabilityTheory
variable {index alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]

theorem MarkovProcess.Kernel.eq_of_map_finiteRestriction_eq
    (kappa eta : Kernel beta (index → alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset index,
      kappa.map I.restrict = eta.map I.restrict) :
    kappa = eta := by sorry
