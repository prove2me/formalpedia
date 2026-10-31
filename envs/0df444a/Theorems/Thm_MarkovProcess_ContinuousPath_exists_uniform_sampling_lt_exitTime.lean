-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_exists_uniform_sampling_lt_exitTime
-- name    : MarkovProcess.ContinuousPath.exists_uniform_sampling_lt_exitTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:26.079347+00:00
-- url     : https://prove2.me/theorems/3e781b4b-77d2-41f3-9d5b-1d61e2a89b7b
-- title:
--   MarkovProcess: exists_uniform_sampling_lt_exitTime
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Uniform sampling of a continuous path

A continuous path is uniformly continuous on every bounded time interval, so for each accuracy
`h > 0` a uniform partition of `[0, T]` fine enough makes every consecutive pair of samples closer
than `h` (`ContinuousPath.exists_uniform_sampling`).  Three variants are recorded for use with the
exit time from a set `U`: when the horizon `T` is strictly before the exit time, every sample time
is too (`ContinuousPath.exists_uniform_sampling_lt_exitTime`), so the samples witness a family of
visited sets before the exit; and when the exit time is finite and positive there are times
strictly before it at which the path is within `h` of its exit position
(`ContinuousPath.exists_lt_exitTime_dist_coordinate_exitTime_lt`).  For an open `U` the exit
position lies on `frontier U`, and the third variant carries that conclusion with it
(`ContinuousPath.exists_lt_exitTime_mem_frontier_dist_lt`): a positive exit time already forces
`omega 0 ∈ U`, the hypothesis of `ContinuousPath.coordinate_exitTime_mem_frontier`, so no extra
hypothesis is needed.  The exit position is spelled `(exitTime U omega).toNNReal` throughout, as
in `Path/ExitTime.lean`; `ContinuousPath.untopD_exitTime` converts the `WithTop.untopD` spelling.

No lattice, no covering family and no discrete geometry appears here: the sampling is purely
metric.
-/

open Set
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]









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
# Uniform sampling of a continuous path

A continuous path is uniformly continuous on every bounded time interval, so for each accuracy
`h > 0` a uniform partition of `[0, T]` fine enough makes every consecutive pair of samples closer
than `h` (`ContinuousPath.exists_uniform_sampling`).  Three variants are recorded for use with the
exit time from a set `U`: when the horizon `T` is strictly before the exit time, every sample time
is too (`ContinuousPath.exists_uniform_sampling_lt_exitTime`), so the samples witness a family of
visited sets before the exit; and when the exit time is finite and positive there are times
strictly before it at which the path is within `h` of its exit position
(`ContinuousPath.exists_lt_exitTime_dist_coordinate_exitTime_lt`).  For an open `U` the exit
position lies on `frontier U`, and the third variant carries that conclusion with it
(`ContinuousPath.exists_lt_exitTime_mem_frontier_dist_lt`): a positive exit time already forces
`omega 0 ∈ U`, the hypothesis of `ContinuousPath.coordinate_exitTime_mem_frontier`, so no extra
hypothesis is needed.  The exit position is spelled `(exitTime U omega).toNNReal` throughout, as
in `Path/ExitTime.lean`; `ContinuousPath.untopD_exitTime` converts the `WithTop.untopD` spelling.

No lattice, no covering family and no discrete geometry appears here: the sampling is purely
metric.
-/

open Set
open scoped ENNReal NNReal



variable {alpha : Type*} [PseudoMetricSpace alpha]



open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.exists_uniform_sampling_lt_exitTime (U : Set alpha) (omega : ContinuousPath alpha)
    (T : NNReal) (hT : (T : ℝ≥0∞) < exitTime U omega) (h : ℝ) (hh : 0 < h) :
    ∃ M : ℕ, 0 < M ∧
      (∀ k ≤ M, (((k : NNReal) * T / (M : NNReal) : NNReal) : ℝ≥0∞) < exitTime U omega) ∧
      ∀ k < M, dist (omega ((k : NNReal) * T / (M : NNReal)))
        (omega (((k : NNReal) + 1) * T / (M : NNReal))) < h := by sorry
