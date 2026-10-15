-- Prove2me | Theorems.Thm_Light_sort_meets
-- name    : Light.sort_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:46:03.059795+00:00
-- url     : https://prove2.me/theorems/3f557316-59bf-4317-b17f-d1fa3afc3d7e
-- title:
--   Merge sort returns a sorted permutation within its resource budget
-- statement:
--   Let a memory segment at address $a$ contain an integer list $L$ of length $n$. Suppose the program contains the specified recursive sort, halving, merge, and copy procedures. Write $S,B,D$ for its space, word, and depth limits, and assume
--   $$S\le B,\quad 1\le B,\quad a+n\le f,\quad f+n\le S,\quad d+\operatorname{clog}_2n+1\le D.$$
--   The call at depth $d$ using scratch base $f$ terminates within
--   $$61n\operatorname{clog}_2n+74(n-1)_++4$$
--   steps. Here $\operatorname{clog}_2n$ is the natural ceiling logarithm, taking value zero at zero. The output segment contains a nondecreasing list $L'$ with $L'\sim L$ as a permutation. Every cell below $f$ outside $[a,a+n)$ keeps its initial value.
--
--   This is the sorting contract used to arrange input values while retaining all indexed occurrences.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/MergeSort.lean#L199-L217

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
import Theorems.Thm_Light_MergeSort_body_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.sort_meets : ∀ {lim : Light.Limits} {P : Light.Program} {pSort pHalf pMerge pCopy : Nat}
  (C : Light.MergeSort.Procs P pSort pHalf pMerge pCopy)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (h1 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word) {a fr : Nat}
  {L : List.{0} Int} {μ : Nat → Int} (hseg : Light.Seg μ a L)
  (haf :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a (@List.length.{0} Int L)) fr)
  (hfr :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fr (@List.length.{0} Int L)) lim.space)
  (d : Nat),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int L)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth →
    Light.Meets lim P pSort d
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int L))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int))))
      μ (Light.sortTime (@List.length.{0} Int L)) fun (x : Int) => Light.MergeSort.Sorted μ a fr L := by
  sorry
