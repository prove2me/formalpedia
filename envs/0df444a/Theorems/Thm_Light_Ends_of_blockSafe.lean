-- Prove2me | Theorems.Thm_Light_Ends_of_blockSafe
-- name    : Light.Ends.of_blockSafe
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:32:48.631298+00:00
-- url     : https://prove2.me/theorems/859e8a72-f984-4030-8bbf-2e070d2c9e0f
-- title:
--   Safe blocks yield bounded executions
-- statement:
--   Fix resource limits, a program, and a call depth. Let $s$ be a statement, $\sigma$ an initial state, $T\in\mathbb N$ a budget, and $Q$ a predicate on final states. Suppose the block-safety predicate holds for $s$ at $\sigma$, its static block cost is at most $T$, and its computed final state $\operatorname{after}(s,\sigma)$ satisfies $Q$. Then there are a final state $\sigma'$ and an execution cost $t$ such that
--
--   $$\operatorname{Exec}(s,\sigma,\sigma',t)\;\land\;t\le T\;\land\;Q(\sigma').$$
--
--   This connects the compositional safety and evaluation rules for finite blocks to the operational execution relation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Rules.lean#L138-L154

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.Ends.of_blockSafe : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {s : Light.Stmt} {σ : Light.State} {T : Nat}
  {Q : Light.State → Prop},
  Light.Stmt.BlockSafe lim s σ → @LE.le.{0} Nat instLENat s.blockCost T → Q (s.after σ) → Light.Ends lim P d s σ T Q := by
  sorry
