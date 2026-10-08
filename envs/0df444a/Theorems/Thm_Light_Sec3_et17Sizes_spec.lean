-- Prove2me | Theorems.Thm_Light_Sec3_et17Sizes_spec
-- name    : Light.Sec3.et17Sizes_spec
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T09:19:47.433752+00:00
-- url     : https://prove2.me/theorems/fe741711-bc3b-45d6-9569-1413feb45590
-- title:
--   The triangle host selects its prime and prepares sizes and addresses
-- statement:
--   Assume the Theorem 17 host context, a valid stored triangle instance, the large-case inequalities for parameters $D,g$, and sufficient execution resources. Starting from its parameter-stage local frame, the host's second stage produces the specified next-stage frame containing the selected prime, query capacity, piece size and count, input bit length, and workspace addresses. Every memory cell below the free pointer is preserved.
--
--   Its time allowance is the sum of the declared prime-selection, query-capacity, two ceiling-division, and bit-length costs, plus $120$. The two divisions compute $\lceil\lfloor\sqrt D\rfloor/g\rceil$ and the number of pieces of the $n$ vertices.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Host/PrimeStage.lean#L99-L127).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Host/PrimeStage.lean#L99-L127

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_ZOrder
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_APSPSource_ThreeSumApsp_Util_PrimesInWindow
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

theorem Light.Sec3.et17Sizes_spec : ∀ {lim : Light.Limits} {d : Nat} {P₀ R : Light.Program} {ν : Light.Sec3.Et17Nums} {Tn : List.{0} Nat → Nat}
  {need : List.{0} Nat → Light.Need} {Dfun Gfun tD tG wD wG : Nat → Nat},
  Light.Sec3.Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG →
    ∀ (x : Light.TriInst) (μ : Nat → Int) (fr D g a b : Nat),
      x.Pre μ fr →
        Light.Sec3.BigCase x.n D g →
          (Light.Sec3.hostNeedAt a b need x.n x.U D g).Ok lim fr d →
            Light.Ends lim
              (@HAppend.hAppend.{0, 0, 0} Light.Program Light.Program Light.Program
                (@instHAppendOfAppend.{0} Light.Program (@List.instAppend.{0} Light.Stmt)) P₀ R)
              d (Light.Sec3.et17Sizes ν) { loc := Light.frame (Light.Sec3.et17LocA x fr D g), mem := μ }
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (Light.Sec3.chooseTime x.n x.U D)
                        (Light.Sec3.tQueryCapNat x.n D))
                      (Light.Sec3.tCeilDiv D.sqrt g))
                    (Light.Sec3.tCeilDiv x.n (ThreeSumApsp.Spec.pieceSizeNat D g)))
                  (Light.Sec3.tBitLen x.U))
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              fun (σ' : Light.State) =>
              ∃ (μ' : Nat → Int),
                And (@Eq.{1} Light.State σ' { loc := Light.frame (Light.Sec3.et17LocB x fr D g), mem := μ' })
                  (Light.Kept μ μ' fr) := by
  sorry
