-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_standardBorelSpace_borel
-- name    : MarkovProcess.ContinuousPath.standardBorelSpace_borel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:31.535206+00:00
-- url     : https://prove2.me/theorems/f7889096-57a3-4389-b3ee-c9bee927b293
-- title:
--   MarkovProcess: standardBorelSpace_borel
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Polish structure of continuous-path space

For a complete separable metric state space, the compact-open topology on continuous paths is
Polish: it is second countable, and it is induced by the compact-convergence uniformity, which is
complete and countably generated because nonnegative time is locally compact and sigma-compact.
With the Borel sigma-algebra the path space is therefore a standard Borel space.

This is ordinary topological infrastructure.  It proves no probabilistic statement.
-/

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]





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
# Polish structure of continuous-path space

For a complete separable metric state space, the compact-open topology on continuous paths is
Polish: it is second countable, and it is induced by the compact-convergence uniformity, which is
complete and countably generated because nonnegative time is locally compact and sigma-compact.
With the Borel sigma-algebra the path space is therefore a standard Borel space.

This is ordinary topological infrastructure.  It proves no probabilistic statement.
-/


variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]



open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.standardBorelSpace_borel :
    @StandardBorelSpace (ContinuousPath alpha) (borel (ContinuousPath alpha)) := by sorry
