-- Prove2me | Theorems.Thm_Light_powTable_ends
-- name    : Light.powTable_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:04:16.070444+00:00
-- url     : https://prove2.me/theorems/bbc4ebfe-dea5-4e30-8458-65484486bb09
-- title:
--   Correctness and cost of writing a table of powers
-- statement:
--   Let $b,L,\mathrm{dst}$ be natural numbers and $\mu$ an initial memory. Suppose $\mathrm{dst}+L\le\mathrm{space}\le\mathrm{word}$ and $b^j\le\mathrm{word}$ for every $j\le L$. Start the Light power-table body with argument locals $(\mathrm{dst},L,b)$, arbitrary values in its exponent and power scratch locals, and any trailing list of locals.
--
--   In any program and depth context it terminates within $17L+8$ steps, with final memory $\nu$ satisfying
--   $$
--   \nu(\mathrm{dst}+j)=b^j\quad(0\le j<L),\qquad
--   \nu(a)=\mu(a)\quad\bigl(a\notin[\mathrm{dst},\mathrm{dst}+L)\bigr).
--   $$
--   The bound on powers includes $b^L$, the final multiplication result. This certifies a reusable primitive for constructing positional-power tables.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean#L68-L103

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
import Mathlib.Data.Int.SuccPred
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
import Theorems.Thm_Light_Ends_for


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light.PowTable
end Light.PowTable
namespace ThreeSumApsp
end ThreeSumApsp

theorem Light.powTable_ends : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int} {dst L b : Nat} (e p : Int) (t : List.{0} Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hdst : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst L) lim.space)
  (hpow :
    ∀ (j : Nat),
      @LE.le.{0} Nat instLENat j L →
        @LE.le.{0} Int Int.instLEInt
          (@Nat.cast.{0} Int instNatCastInt
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) b j))
          lim.word),
  Light.Ends lim P d Light.powTableBody
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                (@List.cons.{0} Int e (@List.cons.{0} Int p t))))),
      mem := μ }
    (Light.powTableTime L) fun (σ' : Light.State) =>
    And (Light.Seg σ'.mem dst (Light.powList b L)) (Light.SameOutside μ σ'.mem dst L) := by
  sorry
