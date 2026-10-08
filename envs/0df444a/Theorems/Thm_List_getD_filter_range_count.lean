-- Prove2me | Theorems.Thm_List_getD_filter_range_count
-- name    : List.getD_filter_range_count
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:47:26.16486+00:00
-- url     : https://prove2.me/theorems/2e52d440-4087-41e6-995b-c562443de9f4
-- title:
--   The rank of an element in a filtered initial interval
-- statement:
--   Let $q$ be a decidable predicate on the natural numbers, and let $L$ be the increasing list of integers $j<n$ satisfying $q(j)$. If $i<n$ and $q(i)$, then its zero-based position in $L$ is the number of satisfying integers below $i$:
--
--   $$L\bigl[\#\{j<i:q(j)\}\bigr]=i.$$
--
--   The formal statement uses list lookup with default value $0$; the hypotheses ensure that this lookup selects the actual entry. This connects predicate counts with the positions used by the source's enumeration routines.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L343-L359).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Util/List.lean#L343-L359

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem List.getD_filter_range_count : ∀ (q : Nat → Prop) [inst : @DecidablePred.{1} Nat q] (n : Nat) {i : Nat},
  @LT.lt.{0} Nat instLTNat i n →
    q i →
      @Eq.{1} Nat
        (@List.getD.{0} Nat (@List.filter.{0} Nat (fun (j : Nat) => @Decidable.decide (q j) (inst j)) (List.range n))
          (@Nat.count q inst i) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        i := by
  sorry
