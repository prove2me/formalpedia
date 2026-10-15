-- Prove2me | Theorems.Thm_Light_MergeSort_body_ends
-- name    : Light.MergeSort.body_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:32:38.830236+00:00
-- url     : https://prove2.me/theorems/0f1f064b-1a9a-4e00-a044-fe0552f517f0
-- title:
--   Inductive execution contract for the merge-sort body
-- statement:
--   Let a Light program contain the recursive sort, halving, merge and copy bodies. Suppose memory $\mu$ stores an integer list $L$ of length $n$ at $a$, with $a+n\le f$, $f+n\le\mathrm{space}\le\mathrm{word}$, $1\le\mathrm{word}$, and current depth $d<\mathrm{depth}$. When $n>1$, assume every stored list of length $m$ with $2m\le n+1$, ending before $f$, satisfies the sorting contract at depth $d+1$ within $S(m)$ steps, for arbitrary initial memory.
--
--   Starting the sort body with locals $(n,a,f)$ terminates within
--   $$
--   S(n)=61n\lceil\log_2 n\rceil+74(n-1)_++4
--   $$
--   steps, where the ceiling-log convention is zero at $n=0$. Its final memory stores a nondecreasing permutation of $L$ at $a$ and preserves every cell below $f$ outside $[a,a+n)$.
--
--   This is the compositional induction step for the recursive sorter.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L152-L197

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
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_Light_MergeSort_clog_split
import Theorems.Thm_Light_half_meets
import Theorems.Thm_Light_merge_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp

theorem Light.MergeSort.body_ends : ∀ {lim : Light.Limits} {P : Light.Program} {pSort pHalf pMerge pCopy : Nat}
  (C : Light.MergeSort.Procs P pSort pHalf pMerge pCopy)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (h1 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word)
  {d a fr : Nat} {L : List.{0} Int} {μ : Nat → Int} (hseg : Light.Seg μ a L)
  (haf :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a (@List.length.{0} Int L)) fr)
  (hfr :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fr (@List.length.{0} Int L)) lim.space)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (ih :
    ∀ (a' : Nat) (L' : List.{0} Int) (μ' : Nat → Int),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.length.{0} Int L) →
        @LE.le.{0} Nat instLENat
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int L'))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int L)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Light.Seg μ' a' L' →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a' (@List.length.{0} Int L')) fr →
              Light.Meets lim P pSort
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int L'))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a')
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int))))
                μ' (Light.sortTime (@List.length.{0} Int L')) fun (x : Int) => Light.MergeSort.Sorted μ' a' fr L'),
  Light.Ends lim P d (Light.sortBody pSort pHalf pMerge pCopy)
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int L))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int)))),
      mem := μ }
    (Light.sortTime (@List.length.{0} Int L)) fun (σ' : Light.State) => Light.MergeSort.Sorted μ a fr L σ'.mem := by
  sorry
