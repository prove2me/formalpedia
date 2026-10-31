-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_restrict_map_shift_eq_pathKernel_comp_of_rational_joint
-- name    : MarkovProcess.ContinuousPath.restrict_map_shift_eq_pathKernel_comp_of_rational_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:23.033744+00:00
-- url     : https://prove2.me/theorems/7093160f-4136-4261-8103-92995581058a
-- title:
--   MarkovProcess: restrict_map_shift_eq_pathKernel_comp_of_rational_joint
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_DenseFiltration_62a9879d
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Restart_RationalRestrictedRestart_3bd46ae7
import Definitions.Def_MarkovProcess_V3H_Restart_RestrictedRestartOfJoint_e84e7ad8
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]









end
end ContinuousPath
end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

open MeasureTheory ProbabilityTheory



variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]







open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.restrict_map_shift_eq_pathKernel_comp_of_rational_joint
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (S : DenseTime)
    (hJoint :
      (Q x).map (fun omega ↦
          (densePastRestriction S omega,
            shift (DenseTime.castOrderEmbedding S) omega)) =
        ((Q x).map (densePastRestriction S)) ⊗ₘ
          Kernel.comap Q (densePastTerminal S) (measurable_densePastTerminal S)) :
    ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha)
        (DenseTime.castOrderEmbedding S)] A →
        ((Q x).restrict A).map (shift (DenseTime.castOrderEmbedding S)) =
          Kernel.comap Q
              (coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding S))
              (measurable_coordinateProcess (DenseTime.castOrderEmbedding S)) ∘ₘ
            ((Q x).restrict A) := by sorry
