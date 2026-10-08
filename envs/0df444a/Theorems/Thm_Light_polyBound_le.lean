-- Prove2me | Theorems.Thm_Light_polyBound_le
-- name    : Light.polyBound_le
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T07:54:40.363432+00:00
-- url     : https://prove2.me/theorems/332539ec-b2f2-4479-bdcb-9a804116d1aa
-- title:
--   Admissible word sizes accommodate polynomial bounds
-- statement:
--   Let $p_1,\ldots,p_\ell$ be natural-number instance parameters, with $\ell\le r$. Let $b,W,s,k,r\in\mathbb N$ satisfy $s+kr+k\le b$ and the admissible-width condition
--
--   $$b\left(\sum_{j=1}^{\ell}\lfloor\log_2p_j\rfloor+1\right)\le W.$$
--
--   Using the source convention $\operatorname{log2}(0)=0$, the polynomial parameter bound fits below $2^W$:
--
--   $$2^s\left(\prod_{j=1}^{\ell}(p_j+1)\right)^k\le2^W.$$
--
--   This translates polynomial bounds on intermediate values into sufficient word widths for the implementation.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/WordSize.lean#L54-L68).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/WordSize.lean#L54-L68

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem Light.polyBound_le : ∀ {b W s k r : Nat} {params : List.{0} Nat},
  ThreeSumApsp.WordRam.Admissible b params W →
    @LE.le.{0} Nat instLENat (@List.length.{0} Nat params) r →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k r))
            k)
          b →
        @LE.le.{0} Nat instLENat (Light.polyBound s k params)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W) := by
  sorry
