-- Prove2me | Theorems.Thm_Light_merge_meets
-- name    : Light.merge_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:37:33.751531+00:00
-- url     : https://prove2.me/theorems/3000e9b5-b10b-4406-bbb4-debdd2bf2ea4
-- title:
--   Verified merging of two stored integer lists
-- statement:
--   Let integer lists $L,R$ be stored in memory $\mu$ at bases $a,b$, and write $n=|L|+|R|$. Assume the two source segments and the destination segment $[z,z+n)$ fit within the machine space bound, the destination is disjoint from each source segment, and space does not exceed the word bound. If the called procedure in $P$ is the merge body, then at any call depth it finishes within $40n+12$ steps with
--
--   $$
--   \nu[z:z+n]=\operatorname{merge}(L,R),\qquad\nu(x)=\mu(x)\quad(x\notin[z,z+n)).
--   $$
--
--   The merge takes the left head unless the right head is smaller. The inputs need not be sorted, and the theorem imposes no numerical bound on their entries. This supplies the exact list-merge primitive used by normalization.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Merge.lean#L155-L194

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_of_blockSafe
import Theorems.Thm_Light_Ends_while
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp

theorem Light.merge_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int} {a b dst : Nat} {l r : List.{0} Int} {p : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt Light.mergeBody))
  (C : Light.Merge.Pre lim μ a b dst l r),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int l))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int r))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))
    μ
    (Light.mergeTime
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int l)
        (@List.length.{0} Int r)))
    fun (x : Int) (μ' : Nat → Int) =>
    And
      (Light.Seg μ' dst
        (@List.merge.{0} Int l r fun (a b : Int) => @Decidable.decide (@LE.le.{0} Int Int.instLEInt a b) (a.decLe b)))
      (Light.SameOutside μ μ' dst
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int l)
          (@List.length.{0} Int r))) := by
  sorry
