-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_eventually_forall_mem_norm_apply_le_of_isCompact
-- name    : MarkovProcess.Semigroup.eventually_forall_mem_norm_apply_le_of_isCompact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:41:26.163401+00:00
-- url     : https://prove2.me/theorems/fa9148be-0fd2-45a3-99ea-75a051fb6876
-- title:
--   Equibounded strong operator convergence is uniform on compact subsets
-- statement:
--   Let $E$ and $F$ be real normed vector spaces and let $T_i : E \to F$ be bounded linear maps, uniformly bounded in operator norm by a constant $C$. If $T_i x$ converges to zero for every fixed $x$, then $T_i x$ converges to zero uniformly on every compact subset $K$ of $E$. For each $\varepsilon > 0$, eventually $\|T_i x\| \le \varepsilon$ for all $x \in K$. The argument uses a finite net and the uniform operator-norm bound.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Semigroup/CompactStrongConvergence.lean#L28-L73

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Normed.Operator.Basic
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem MarkovProcess.Semigroup.eventually_forall_mem_norm_apply_le_of_isCompact {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] F) {C : ℝ} (hC : ∀ i, ‖T i‖ ≤ C)
    (hT : ∀ x, Tendsto (fun i ↦ T i x) l (𝓝 0))
    {K : Set E} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ K, ‖T i x‖ ≤ ε := by sorry
