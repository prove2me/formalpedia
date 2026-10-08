-- Prove2me | Theorems.Thm_Light_Sec3_et17_spec
-- name    : Light.Sec3.et17_spec
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T09:38:58.184515+00:00
-- url     : https://prove2.me/theorems/e7a8c6a0-dbdf-4946-8767-fb35ce5b328d
-- title:
--   The concrete Theorem 17 host correctly decides Exact Triangle
-- statement:
--   Let three integer weight matrices describe a tripartite instance with $n\ge1$ vertices per part and weights of absolute value at most $U\ge1$. Suppose their arrays lie below a free-memory address $f$, the program contains the specified sparse-triangle solver and host procedures, and the execution limits meet the defined host resource requirement.
--
--   Then the concrete Theorem 17 host terminates within its defined $\operatorname{hostTime}$ bound and returns
--
--   $$r=\begin{cases}1,&\exists a,b,c<n:\;w_{AB}(a,b)+w_{BC}(b,c)+w_{AC}(a,c)=0,\\0,&\text{otherwise}.\end{cases}$$
--
--   Every memory cell below $f$ is preserved. The theorem is uniform in the supplied parameter procedures and solver time/resource functions, subject to the explicit host-context contract. It proves correctness and the concrete execution budget used in the later asymptotic analysis.
--
--   References:
--
--   1. [Source formalization](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Host/Correct.lean#L29-L70).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Host/Correct.lean#L29-L70

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
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_ZOrder
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
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
import Mathlib.Combinatorics.Enumerative.DoubleCounting
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

theorem Light.Sec3.et17_spec : ∀ {P₀ R : Light.Program} {ν : Light.Sec3.Et17Nums} {Tn : List.{0} Nat → Nat} {need : List.{0} Nat → Light.Need}
  {Dfun Gfun tD tG wD wG : Nat → Nat},
  Light.Sec3.Et17Ctx P₀ R ν Tn need Dfun Gfun tD tG wD wG →
    ∀ {lim : Light.Limits} {d : Nat} (x : Light.TriInst) (μ : Nat → Int) (fr : Nat),
      x.Pre μ fr →
        (Light.Sec3.hostNeed Dfun Gfun wD wG need x.n x.U).Ok lim fr d →
          Light.Ends lim
            (@HAppend.hAppend.{0, 0, 0} Light.Program Light.Program Light.Program
              (@instHAppendOfAppend.{0} Light.Program (@List.instAppend.{0} Light.Stmt)) P₀ R)
            d (Light.Sec3.et17Body ν)
            {
              loc :=
                Light.frame
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.n)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.U)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.ab)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.bc)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt x.ac)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr) (@List.nil.{0} Int))))))),
              mem := μ }
            (Light.Sec3.hostTime Dfun Gfun tD tG Tn x.n x.U) fun (σ' : Light.State) =>
            Light.etTask.Post x μ fr (σ'.loc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) σ'.mem := by
  sorry
