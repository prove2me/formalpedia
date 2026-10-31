-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_canonicalDiscreteLaw_map_coordinate_zero
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.canonicalDiscreteLaw_map_coordinate_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:28.348085+00:00
-- url     : https://prove2.me/theorems/fcde5030-cf5a-4945-9f39-873e66f1f0e1
-- title:
--   MarkovProcess: canonicalDiscreteLaw_map_coordinate_zero
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscreteLaw_ed3fbdc7
import Definitions.Def_MarkovProcess_V3H_DenseTime_CanonicalDiscretePath_a2b715fb
import Definitions.Def_MarkovProcess_V3H_Time_OrderedGrid_1c9977ee
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete trajectory laws

This file equips the canonical discrete path space with the trajectory law of
a conservative transition-kernel semigroup along one fixed ordered grid.  It
records exact finite-prefix and coordinate marginal identities.  No
conditional-expectation Markov property is asserted here.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)











end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Canonical discrete trajectory laws

This file equips the canonical discrete path space with the trajectory law of
a conservative transition-kernel semigroup along one fixed ordered grid.  It
records exact finite-prefix and coordinate marginal identities.  No
conditional-expectation Markov property is asserted here.
-/

open MeasureTheory
open ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]


variable (P : SubMarkovKernelSemigroup α)









open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.canonicalDiscreteLaw_map_coordinate_zero
    (hP : P.IsConservative) (grid : OrderedGrid) (x : α) :
    (canonicalDiscreteLaw P hP grid x).map (DiscretePath.coordinate 0) = Measure.dirac x := by sorry
