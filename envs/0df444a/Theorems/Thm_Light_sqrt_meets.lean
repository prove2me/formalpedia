-- Prove2me | Theorems.Thm_Light_sqrt_meets
-- name    : Light.sqrt_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:35:48.27732+00:00
-- url     : https://prove2.me/theorems/79223a1d-4d33-4cf7-a033-0ccf287b5b97
-- title:
--   Correctness and cost of the integer square-root procedure
-- statement:
--   Fix a program containing the square-root procedure, resource limits, a call depth, and initial memory $\mu$. Let $K\in\mathbb N$ and suppose $3K+4$ fits within the word-magnitude limit. Put $s=\lfloor\sqrt K\rfloor$. The procedure called on $K$ returns
--
--   $$r=s,\qquad\mu'=\mu,\qquad\text{cost}\le18s+12.$$
--
--   This contract verifies the exact rounded square root and its finite cost, including $K=0$, for the schedule's arithmetic routines.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Sqrt.lean#L47-L77

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
import Theorems.Thm_Light_Ends_of_blockSafe
import Theorems.Thm_Light_Ends_while


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.sqrt_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p K : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt Light.sqrtBody))
  (μ : Nat → Int)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) K)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      lim.word),
  Light.Meets lim P p d (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K) (@List.nil.{0} Int)) μ
    (Light.sqrtTime K) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt K.sqrt)) (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
