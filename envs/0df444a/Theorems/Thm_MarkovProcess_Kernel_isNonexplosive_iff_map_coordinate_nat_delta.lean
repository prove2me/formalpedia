-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_isNonexplosive_iff_map_coordinate_nat_delta
-- name    : MarkovProcess.Kernel.isNonexplosive_iff_map_coordinate_nat_delta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:40.437442+00:00
-- url     : https://prove2.me/theorems/07840e20-c6d0-4da8-bae0-20ee37747a12
-- title:
--   MarkovProcess: isNonexplosive_iff_map_coordinate_nat_delta
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

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
# Detecting nonexplosion from countably many coordinates

For a lifetime path, infinite lifetime is equivalent to being alive at every natural-number
time. Consequently, nonexplosion of a lifetime-path kernel can be proved from countably many
almost-sure coordinate statements. This is the measure-theoretic reduction later used to turn
conservativity of transition laws into nonexplosion.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]



end LifetimePath

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]





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
# Detecting nonexplosion from countably many coordinates

For a lifetime path, infinite lifetime is equivalent to being alive at every natural-number
time. Consequently, nonexplosion of a lifetime-path kernel can be proved from countably many
almost-sure coordinate statements. This is the measure-theoretic reduction later used to turn
conservativity of transition laws into nonexplosion.
-/

open MeasureTheory
open scoped ENNReal NNReal





variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]



open MarkovProcess.Kernel in

theorem MarkovProcess.Kernel.isNonexplosive_iff_map_coordinate_nat_delta
    (kappa : ProbabilityTheory.Kernel beta (LifetimePath alpha)) :
    IsNonexplosive kappa ↔
      ∀ n : ℕ, ∀ x,
        kappa.map (LifetimePath.coordinate (n : NNReal)) x {Cemetery.delta} = 0 := by sorry
