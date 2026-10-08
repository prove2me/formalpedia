-- Prove2me | Theorems.Thm_Light_Exec_mem_outside
-- name    : Light.Exec.mem_outside
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:33.556407+00:00
-- url     : https://prove2.me/theorems/ac855574-7865-42f7-aea0-2f7c43b07ef3
-- title:
--   Execution preserves memory beyond the declared space limit
-- statement:
--   Fix a program $P$, execution limits $\mathrm{lim}$, and call depth $d$. Suppose statement $s$ runs from state $\sigma$ to state $\sigma'$ in exactly $c$ steps according to the source execution semantics. For every natural address $a\ge\mathrm{lim.space}$,
--
--   $$\sigma'.\operatorname{mem}(a)=\sigma.\operatorname{mem}(a).$$
--
--   Thus a legal run cannot change cells outside its declared memory region. This preservation property is used when composing program fragments and proving that separately allocated data remain intact.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/RunsStayInLimits.lean#L81-L95).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/RunsStayInLimits.lean#L81-L95

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.Exec.mem_outside : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {s : Light.Stmt} {σ σ' : Light.State} {c : Nat},
  Light.Exec lim P d s σ σ' c → ∀ (a : Nat), @LE.le.{0} Nat instLENat lim.space a → @Eq.{1} Int (σ'.mem a) (σ.mem a) := by
  sorry
