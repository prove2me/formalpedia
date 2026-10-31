-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_cemeteryDenseTimeTrajectory_map_eval_alive_delta
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.cemeteryDenseTimeTrajectory_map_eval_alive_delta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:22.399701+00:00
-- url     : https://prove2.me/theorems/1a8799ba-43af-429c-8bad-2652e9f56392
-- title:
--   MarkovProcess: cemeteryDenseTimeTrajectory_map_eval_alive_delta
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery marginals of dense-time trajectories

For a conservative live semigroup, the trajectory of its cemetery extension has no cemetery mass
at any dense-time coordinate when started from a live state.  This is a finite-coordinate statement;
it does not assert that a dense-time path has a continuous lifetime-path extension.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess
namespace SubMarkovKernelSemigroup
namespace IsConservative

noncomputable section

variable {D alpha : Type*} [MeasurableSpace alpha] [StandardBorelSpace (Cemetery alpha)]



end
end IsConservative
end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery marginals of dense-time trajectories

For a conservative live semigroup, the trajectory of its cemetery extension has no cemetery mass
at any dense-time coordinate when started from a live state.  This is a finite-coordinate statement;
it does not assert that a dense-time path has a continuous lifetime-path extension.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal



variable {D alpha : Type*} [MeasurableSpace alpha] [StandardBorelSpace (Cemetery alpha)]

open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.cemeteryDenseTimeTrajectory_map_eval_alive_delta
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (d : D) (x : alpha) :
    ((denseTimeTrajectory P.cemeterySemigroup P.isConservative_cemeterySemigroup e iota).map
        (fun path ↦ path d)) (Cemetery.alive x) {Cemetery.delta} = 0 := by sorry
