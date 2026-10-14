-- Prove2me | Theorems.Thm_Light_Ends_while
-- name    : Light.Ends.while
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:32:36.72329+00:00
-- url     : https://prove2.me/theorems/e80bb672-49c9-4d40-ae8b-a4a4d86a8ba5
-- title:
--   A loop invariant with an explicit total cost
-- statement:
--   Fix resource limits, a program, a call depth, an initial state $\sigma$, a condition $c$, and a loop body $s$. Let $I_i$ be a state predicate for each $i\in\mathbb N$, let $n$ be the number of iterations, and let $b_i$ bound iteration $i$'s body cost. Assume $I_0(\sigma)$. Whenever $i<n$ and $I_i$ holds, the condition is safe and true, and the body terminates within $b_i$ steps in a state satisfying $I_{i+1}$. Whenever $I_n$ holds, the condition is safe and false and the desired postcondition $Q$ holds.
--
--   The loop terminates with $Q$, within the cost
--
--   $$T=\sum_{i=0}^{n-1}\bigl(\operatorname{cost}(c)+1+b_i\bigr)+\operatorname{cost}(c)+1.$$
--
--   This rule combines an indexed loop invariant with a finite execution budget, including the final unsuccessful condition test.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Logic.lean#L134-L161

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.Ends.while : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {σ : Light.State} {c : Light.Cond} {s : Light.Stmt}
  {Q : Light.State → Prop} (I : Nat → Light.State → Prop) (n : Nat) (b : Nat → Nat)
  (hI : I (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) σ)
  (hs :
    ∀ (i : Nat) (σ : Light.State),
      @LT.lt.{0} Nat instLTNat i n →
        I i σ →
          And (Light.Cond.Safe lim σ c)
            (And (Light.Cond.Holds σ c)
              (Light.Ends lim P d s σ (b i)
                (I
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
  (hn : ∀ (σ : Light.State), I n σ → And (Light.Cond.Safe lim σ c) (And (Not (Light.Cond.Holds σ c)) (Q σ))),
  Light.Ends lim P d (Light.Stmt.while c s) σ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (∑ i ∈ Finset.range n,
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.cost
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (b i))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.cost
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    Q := by
  sorry
