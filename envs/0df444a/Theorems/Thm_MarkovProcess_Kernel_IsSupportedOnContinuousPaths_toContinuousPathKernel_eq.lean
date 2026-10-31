-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_IsSupportedOnContinuousPaths_toContinuousPathKernel_eq
-- name    : MarkovProcess.Kernel.IsSupportedOnContinuousPaths.toContinuousPathKernel_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:27.956581+00:00
-- url     : https://prove2.me/theorems/9ce68e9f-5e8c-4fe5-b4ca-9fcc53c6e2f9
-- title:
--   MarkovProcess: toContinuousPathKernel_eq
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
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
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]













end Kernel
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

open MeasureTheory ProbabilityTheory Set




variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]









open MarkovProcess.Kernel in

theorem MarkovProcess.Kernel.IsSupportedOnContinuousPaths.toContinuousPathKernel_eq
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default₁ default₂ : ContinuousPath alpha) :
    toContinuousPathKernel κ default₁ = toContinuousPathKernel κ default₂ := by sorry
