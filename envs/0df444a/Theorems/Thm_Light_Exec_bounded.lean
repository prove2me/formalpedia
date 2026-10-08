-- Prove2me | Theorems.Thm_Light_Exec_bounded
-- name    : Light.Exec.bounded
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:48.223978+00:00
-- url     : https://prove2.me/theorems/3a4a708b-44c0-49c0-bad6-c66cd50d2360
-- title:
--   Execution preserves the bound on stored words
-- statement:
--   Fix a program $P$, execution limits $\mathrm{lim}$, and call depth $d$. Suppose statement $s$ executes from $\sigma$ to $\sigma'$ in $c$ steps. If every local variable and memory cell of $\sigma$ has absolute value at most $\mathrm{lim.word}$, then the same is true in $\sigma'$:
--
--   $$\bigl(\forall x,\ |\sigma.\operatorname{loc}(x)|\le\mathrm{lim.word}\bigr)\ \land\ \bigl(\forall a,\ |\sigma.\operatorname{mem}(a)|\le\mathrm{lim.word}\bigr)\ \Longrightarrow\ \operatorname{Bounded}_{\mathrm{lim}}(\sigma').$$
--
--   This invariant connects the source execution semantics with the finite word sizes required by the word-RAM implementation.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/RunsStayInLimits.lean#L65-L79).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/RunsStayInLimits.lean#L65-L79

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
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

theorem Light.Exec.bounded : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {s : Light.Stmt} {σ σ' : Light.State} {c : Nat},
  Light.Exec lim P d s σ σ' c → Light.State.Bounded lim σ → Light.State.Bounded lim σ' := by
  sorry
