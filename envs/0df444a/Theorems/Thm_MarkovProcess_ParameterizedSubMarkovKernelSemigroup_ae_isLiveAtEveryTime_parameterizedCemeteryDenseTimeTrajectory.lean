-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_ae_isLiveAtEveryTime_parameterizedCemeteryDenseTimeTrajectory
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.ae_isLiveAtEveryTime_parameterizedCemeteryDenseTimeTrajectory
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:44.277405+00:00
-- url     : https://prove2.me/theorems/90f12938-d27d-46bc-b1cc-f1d81ad8364b
-- title:
--   MarkovProcess: ae_isLiveAtEveryTime_parameterizedCemeteryDenseTimeTrajectory
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_TrajectoryMarginals_db9e38cc
import Definitions.Def_MarkovProcess_V3H_Parameterized_CemeteryDenseTimeSupport_55332836
import Definitions.Def_MarkovProcess_V3H_Parameterized_CemeterySemigroup_9e5cada4
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeTrajectory_d8dd1c30
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
# Simultaneous dense-time cemetery avoidance

For conservative live fibers, the jointly constructed parameterized cemetery trajectory avoids
the cemetery state simultaneously at every point of its countable dense-time index.

This is only a statement about the countable trajectory. It makes no continuous-extension,
lifetime-path, or spatial support claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess

noncomputable section



namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]



end ParameterizedSubMarkovKernelSemigroup

end
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Simultaneous dense-time cemetery avoidance

For conservative live fibers, the jointly constructed parameterized cemetery trajectory avoids
the cemetery state simultaneously at every point of its countable dense-time index.

This is only a statement about the countable trajectory. It makes no continuous-extension,
lifetime-path, or spatial support claim.
-/

open MeasureTheory ProbabilityTheory






variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace (Cemetery alpha)]

open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.ae_isLiveAtEveryTime_parameterizedCemeteryDenseTimeTrajectory
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) :
    ∀ᵐ path ∂P.cemeterySemigroup.parameterizedDenseTimeTrajectory
        P.isConservative_cemeterySemigroup e iota (theta, Cemetery.alive x),
      IsLiveAtEveryTime path := by sorry
