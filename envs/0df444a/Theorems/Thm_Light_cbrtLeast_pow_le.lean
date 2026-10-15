-- Prove2me | Theorems.Thm_Light_cbrtLeast_pow_le
-- name    : Light.cbrtLeast_pow_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:34:39.34585+00:00
-- url     : https://prove2.me/theorems/548181dd-770f-404c-af5b-ea4f98871788
-- title:
--   Cubing a rounded-up cube root loses at most a factor of eight
-- statement:
--   For $n\in\mathbb N$, let $r(n)$ be the least natural number $r$ satisfying $n\le r^3$, so $r(n)=\lceil\sqrt[3]{n}\rceil$. Then
--
--   $$r(n)^3\le8n.$$
--
--   The bound includes $n=0$ and gives a uniform finite estimate for algorithms using the rounded cube-root parameter.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/Logs.lean#L165-L177

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light.Logs
end Light.Logs

theorem Light.cbrtLeast_pow_le : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (Light.cbrtLeast n)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) n) := by
  sorry
