-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_isMarkovKernel_toLifetimePathKernel
-- name    : MarkovProcess.Kernel.isMarkovKernel_toLifetimePathKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:33.148312+00:00
-- url     : https://prove2.me/theorems/2e0e127c-57ee-4b40-be12-2b775af1a65f
-- title:
--   MarkovProcess: isMarkovKernel_toLifetimePathKernel
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Law_b2011c24
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous laws as nonexplosive lifetime-path laws

This file transports kernels on ordinary continuous paths through the infinite-lifetime
embedding. It records the resulting nonexplosion and coordinate identities without asserting
that any particular dense-time or PDE law has continuous paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]













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
# Continuous laws as nonexplosive lifetime-path laws

This file transports kernels on ordinary continuous paths through the infinite-lifetime
embedding. It records the resulting nonexplosion and coordinate identities without asserting
that any particular dense-time or PDE law has continuous paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal




variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]







open MarkovProcess.Kernel in

theorem MarkovProcess.Kernel.isMarkovKernel_toLifetimePathKernel
    (kappa : Kernel beta (ContinuousPath alpha)) [IsMarkovKernel kappa] :
    IsMarkovKernel (toLifetimePathKernel kappa) := by sorry
