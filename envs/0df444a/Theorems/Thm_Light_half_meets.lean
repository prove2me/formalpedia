-- Prove2me | Theorems.Thm_Light_half_meets
-- name    : Light.half_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:35:27.083907+00:00
-- url     : https://prove2.me/theorems/80f3c08e-c58d-4234-9f2a-1f5c1d24c6ee
-- title:
--   Correctness and cost of rounded-up halving
-- statement:
--   Fix a program containing the halving procedure, resource limits, a call depth, and initial memory $\mu$. Let $h\in\mathbb N$, and suppose $h+1$ fits within the word-magnitude limit. Put $c=\lceil h/2\rceil=(h+1)\mathbin{/}2$. The procedure called on $h$ returns
--
--   $$r=c,\qquad\mu'=\mu,\qquad\text{cost}\le10c+10.$$
--
--   This gives the exact rounded half used to split recursive subproblems, with a budget valid also at $h=0$.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L251-L271

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_of_blockSafe
import Theorems.Thm_Light_Ends_while


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light.Logs
end Light.Logs

theorem Light.half_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p h : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt Light.halfBody))
  (μ : Nat → Int)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.word),
  Light.Meets lim P p d (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h) (@List.nil.{0} Int)) μ
    (Light.halfTime h) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
