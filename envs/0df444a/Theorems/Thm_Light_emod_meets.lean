-- Prove2me | Theorems.Thm_Light_emod_meets
-- name    : Light.emod_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:23.773167+00:00
-- url     : https://prove2.me/theorems/0d9ab5ce-77c3-4ec1-85f4-7e996746cf35
-- title:
--   Verified signed Euclidean remainder with logarithmic scratch space
-- statement:
--   Let $x\in\mathbb Z$ and $M,V,f\in\mathbb N$ satisfy $M\ge1$ and $|x|\le V$. Let $S,W$ be the machine space and word bounds, with $S\le W$, $4V+4M+16\le W$, and $f+\lfloor\log_2(V+1)\rfloor+2\le S$. If procedure $p$ in program $P$ is the Euclidean-remainder body, then in any initial integer memory $\mu$ and at any depth, execution on $(x,M,f)$ finishes within $43K+34$ steps, where $K$ is the bit length of $\lfloor |x|/M\rfloor$, taking zero to have bit length zero. It produces
--
--   $$
--   r=x\bmod M,\qquad \mu'(q)=\mu(q)\quad(q<f).
--   $$
--
--   Here the remainder is Euclidean. This provides the bounded-machine modular arithmetic used throughout the construction.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L234-L264

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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Emod_reduce_ends
import Theorems.Thm_Light_Emod_sign_ends
import Theorems.Thm_Light_Emod_table_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.emod_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int} {x : Int} {Mo V fr p : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt Light.emodBody))
  (F : Light.Emod.Pre lim Mo V fr)
  (hx :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x) (@Nat.cast.{0} Int instNatCastInt V)),
  Light.Meets lim P p d
    (@List.cons.{0} Int x
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int))))
    μ (Light.emodTime x.natAbs Mo) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod) x (@Nat.cast.{0} Int instNatCastInt Mo)))
      (Light.Kept μ μ' fr) := by
  sorry
