-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_tendsto_zero_of_nonneg_sq_le
-- name    : MarkovProcess.Semigroup.tendsto_zero_of_nonneg_sq_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:13.485261+00:00
-- url     : https://prove2.me/theorems/c6a20c20-5946-441b-a40c-645e3dffba4a
-- title:
--   MarkovProcess: tendsto_zero_of_nonneg_sq_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Mathlib.Analysis.SpecificLimits.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Limits along positive real parameters

This module provides elementary filter limits for positive real resolvent
parameters and a filter-generic criterion that turns a vanishing square bound
into convergence to zero.
-/

namespace MarkovProcess.Semigroup

open Filter Set Topology











end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Limits along positive real parameters

This module provides elementary filter limits for positive real resolvent
parameters and a filter-generic criterion that turns a vanishing square bound
into convergence to zero.
-/


open Filter Set Topology









open MarkovProcess.Semigroup in

theorem MarkovProcess.Semigroup.tendsto_zero_of_nonneg_sq_le {ι : Type*} {l : Filter ι}
    {e r : ι → ℝ}
    (he : ∀ i, 0 ≤ e i)
    (her : ∀ i, (e i) ^ 2 ≤ r i)
    (hr : Tendsto r l (nhds 0)) :
    Tendsto e l (nhds 0) := by sorry
