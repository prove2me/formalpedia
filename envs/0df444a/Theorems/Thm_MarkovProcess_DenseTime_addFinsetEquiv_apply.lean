-- Prove2me | Theorems.Thm_MarkovProcess_DenseTime_addFinsetEquiv_apply
-- name    : MarkovProcess.DenseTime.addFinsetEquiv_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:46.768159+00:00
-- url     : https://prove2.me/theorems/1e5c6091-c7fe-469a-805e-c6d58aca2d65
-- title:
--   MarkovProcess: addFinsetEquiv_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
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
# Finite-coordinate shifts on dense-time paths

Addition by a dense time transports finite sets of dense-time coordinates injectively.  This file
provides the resulting coordinate equivalence and relates restriction after shifting a dense-time
path to restriction on the translated finite set.  It makes no probability-law or Markov claim.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime









end DenseTime

namespace DenseTimePath

variable {alpha : Type*}





variable [MeasurableSpace alpha]





end DenseTimePath
end
end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTime
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-coordinate shifts on dense-time paths

Addition by a dense time transports finite sets of dense-time coordinates injectively.  This file
provides the resulting coordinate equivalence and relates restriction after shifting a dense-time
path to restriction on the translated finite set.  It makes no probability-law or Markov claim.
-/










open MarkovProcess.DenseTime in
@[simp]

theorem MarkovProcess.DenseTime.addFinsetEquiv_apply (s : DenseTime) (I : Finset DenseTime) (t : I) :
    (addFinsetEquiv s I t : DenseTime) = s + t := by sorry
