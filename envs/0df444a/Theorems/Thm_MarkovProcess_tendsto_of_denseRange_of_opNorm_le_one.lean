-- Prove2me | Theorems.Thm_MarkovProcess_tendsto_of_denseRange_of_opNorm_le_one
-- name    : MarkovProcess.tendsto_of_denseRange_of_opNorm_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:58.980492+00:00
-- url     : https://prove2.me/theorems/d55e2322-df21-4951-a92e-30c1ea8d80b8
-- title:
--   MarkovProcess: tendsto_of_denseRange_of_opNorm_le_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_DenseCoreConvergence_48a35d65
import Mathlib.Analysis.Normed.Operator.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence from a dense core

This module extends pointwise convergence of uniformly contractive continuous
linear maps from the range of a dense map to the whole ambient space.
-/

open Filter Topology

namespace MarkovProcess





end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Convergence from a dense core

This module extends pointwise convergence of uniformly contractive continuous
linear maps from the range of a dense map to the whole ambient space.
-/

open Filter Topology


open MarkovProcess in

theorem MarkovProcess.tendsto_of_denseRange_of_opNorm_le_one
    {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} (T : ι → E →L[ℝ] E) (D : F →L[ℝ] E)
    (hT : ∀ i, ‖T i‖ ≤ 1) (hD : DenseRange D)
    (hcore : ∀ v, Tendsto (fun i ↦ T i (D v)) l (nhds (D v))) :
    ∀ f, Tendsto (fun i ↦ T i f) l (nhds f) := by sorry
