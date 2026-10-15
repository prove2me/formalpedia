-- Prove2me | Theorems.Thm_Light_log2_meets
-- name    : Light.log2_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:35:44.44221+00:00
-- url     : https://prove2.me/theorems/e5ed8ef0-84b3-4b49-b0c4-208f0a6e43cf
-- title:
--   Correctness and cost of the floor binary logarithm procedure
-- statement:
--   Fix a program containing the floor-logarithm procedure, resource limits, a call depth, and initial memory $\mu$. For $x\in\mathbb N$, assume $2x+2$ fits within the word-magnitude limit. Let $\ell=\log_2^{\mathrm{nat}}x$, the floor binary logarithm with the total convention $\log_2^{\mathrm{nat}}0=0$. The procedure returns
--
--   $$r=\ell,\qquad\mu'=\mu,\qquad\text{cost}\le14\ell+12.$$
--
--   This supplies the integer logarithm used in the parameter schedule together with an explicit execution budget and preservation of memory.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L62-L94

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

theorem Light.log2_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p x : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt Light.log2Body))
  (μ : Nat → Int)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.word),
  Light.Meets lim P p d (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x) (@List.nil.{0} Int)) μ
    (Light.log2Time x) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
