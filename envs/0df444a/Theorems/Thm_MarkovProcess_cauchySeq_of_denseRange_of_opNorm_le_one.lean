-- Prove2me | Theorems.Thm_MarkovProcess_cauchySeq_of_denseRange_of_opNorm_le_one
-- name    : MarkovProcess.cauchySeq_of_denseRange_of_opNorm_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:32.983069+00:00
-- url     : https://prove2.me/theorems/5411fcdd-147a-4b51-a7ce-3cb856e0fe92
-- title:
--   MarkovProcess: cauchySeq_of_denseRange_of_opNorm_le_one
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

theorem MarkovProcess.cauchySeq_of_denseRange_of_opNorm_le_one
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℕ → E →L[ℝ] E) (D : F →L[ℝ] E)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hD : DenseRange D)
    (hcore : ∀ v, CauchySeq (fun n ↦ T n (D v))) :
    ∀ x, CauchySeq (fun n ↦ T n x) := by sorry
