-- Prove2me | Theorems.Thm_MarkovProcess_Measure_map_denseRestriction_eq_iff
-- name    : MarkovProcess.Measure.map_denseRestriction_eq_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:13.46605+00:00
-- url     : https://prove2.me/theorems/dfe38377-5299-43fb-a0e8-3dd83f5fb915
-- title:
--   MarkovProcess: map_denseRestriction_eq_iff
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Path_MeasureIdentification_8dc880ce
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path measures from dense-time restrictions

A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
deterministic property of continuous paths.
-/

open MeasureTheory

namespace MarkovProcess
namespace Measure

noncomputable section

variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]





end
end Measure
end MarkovProcess


open MarkovProcess
open MarkovProcess.Measure
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path measures from dense-time restrictions

A measure on continuous-path space is determined by its pushforward to the fixed dense time
carrier. This is the measure-level counterpart of continuous-path kernel identification and is a
deterministic property of continuous paths.
-/

open MeasureTheory



variable {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]



open MarkovProcess.Measure in

theorem MarkovProcess.Measure.map_denseRestriction_eq_iff
    {mu nu : MeasureTheory.Measure (ContinuousPath alpha)} :
    mu.map ContinuousPath.denseRestriction = nu.map ContinuousPath.denseRestriction ↔
      mu = nu := by sorry
