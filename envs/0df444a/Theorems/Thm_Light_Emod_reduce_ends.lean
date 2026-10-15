-- Prove2me | Theorems.Thm_Light_Emod_reduce_ends
-- name    : Light.Emod.reduce_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:35:17.521796+00:00
-- url     : https://prove2.me/theorems/155e505c-f564-4880-9285-8593ad506552
-- title:
--   Descending modular subtraction computes the remainder
-- statement:
--   Fix resource limits with memory bound $S$ and word-magnitude bound $W$, a program, and a call depth. Let $M,V,f,a\in\mathbb N$, with $M\ge1$, $a\le V$, $S\le W$, $4V+4M+16\le W$, and $f+\log_2^{\mathrm{nat}}(V+1)+2\le S$. Put $K=\operatorname{bits}(a\mathbin{/}M)$, with $\operatorname{bits}(0)=0$. Suppose memory $\nu$ stores $M2^j$ at $f+j$ for $j<K$ and agrees with a reference memory below $f$. For arbitrary integers $x,t$, the reduction loop has the state transition
--
--   $$([x,M,f,a,K,t],\nu)\longrightarrow([x,M,f,a\bmod M,0,t],\nu)$$
--
--   within $24K+4$ steps. This verifies the read-only subtraction phase of the remainder routine.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Emod.lean#L167-L211

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
import Theorems.Thm_Light_Ends_while


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.Emod.reduce_ends : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int} {x : Int} {Mo V fr a : Nat}
  (F : Light.Emod.Pre lim Mo V fr) (haV : @LE.le.{0} Nat instLENat a V) {μ' : Nat → Int} {t : Int}
  (tab : Light.Emod.Table μ μ' Mo fr (Light.emodRounds a Mo)),
  Light.Ends lim P d Light.emodReduce
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int x
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (Light.emodRounds a Mo))
                    (@List.cons.{0} Int t (@List.nil.{0} Int))))))),
      mem := μ' }
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) (Light.emodRounds a Mo))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
    fun (σ' : Light.State) =>
    @Eq.{1} Light.State σ'
      {
        loc :=
          Light.frame
            (@List.cons.{0} Int x
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr)
                  (@List.cons.{0} Int
                    (@Nat.cast.{0} Int instNatCastInt
                      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a Mo))
                    (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons.{0} Int t (@List.nil.{0} Int))))))),
        mem := μ' } := by
  sorry
