-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_eq_of_map_finitePastDenseFutureRestriction_eq
-- name    : MarkovProcess.Kernel.eq_of_map_finitePastDenseFutureRestriction_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:27.280554+00:00
-- url     : https://prove2.me/theorems/838b9d58-baf3-4837-88b5-0c9f51c32d6a
-- title:
--   MarkovProcess: eq_of_map_finitePastDenseFutureRestriction_eq
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Kernel_FiniteRestrictionIdentification_619c5320
import Definitions.Def_MarkovProcess_V3H_Restart_FinitePastRestart_281c4f1c
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying joint laws of a finite past and a continuous future

A kernel whose values consist of a finite-coordinate past and a continuous future path is
determined by all finite coordinate marginals which retain coordinates from both pieces.  This is
the uniqueness step needed to upgrade finite-dimensional restart identities to a whole-future
joint-law factorization.  It does not assert that any particular stochastic process has those
finite-dimensional identities.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {index alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]













end
end Kernel
end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying joint laws of a finite past and a continuous future

A kernel whose values consist of a finite-coordinate past and a continuous future path is
determined by all finite coordinate marginals which retain coordinates from both pieces.  This is
the uniqueness step needed to upgrade finite-dimensional restart identities to a whole-future
joint-law factorization.  It does not assert that any particular stochastic process has those
finite-dimensional identities.
-/

open MeasureTheory ProbabilityTheory



variable {index alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]











open MarkovProcess.Kernel in

theorem MarkovProcess.Kernel.eq_of_map_finitePastDenseFutureRestriction_eq
    (default : ContinuousPath alpha)
    (kappa eta : Kernel beta ((index → alpha) × ContinuousPath alpha))
    [IsFiniteKernel kappa]
    (h : ∀ I : Finset (index ⊕ DenseTime),
      kappa.map (I.restrict ∘ finitePastDenseFuture) =
        eta.map (I.restrict ∘ finitePastDenseFuture)) :
    kappa = eta := by sorry
