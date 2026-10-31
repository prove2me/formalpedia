-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteSetKernel_map_pullback_translate
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullback_translate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:23.259959+00:00
-- url     : https://prove2.me/theorems/48a5079e-df23-4720-834e-768d0ad61bec
-- title:
--   MarkovProcess: finiteSetKernel_map_pullback_translate
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteSetKernelShift_14b03019
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelShift_4030eb49
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section





















namespace IsConservative

variable {alpha : Type*} [MeasurableSpace alpha]



end IsConservative

end
end SubMarkovKernelSemigroup

namespace DenseTime



end DenseTime
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Translation of finite-set kernels

This file translates finite sets of nonnegative observation times, reindexes paths on the
translated set back to the original coordinates, and proves the corresponding translation law
for conservative transition-kernel semigroups.  It is finite-dimensional kernel infrastructure;
it does not assert a path-space Markov property.
-/

open MeasureTheory ProbabilityTheory
























variable {alpha : Type*} [MeasurableSpace alpha]

open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullback_translate
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (s : NNReal) (I : Finset NNReal) :
    (finiteSetKernel P (finiteSetTranslate s I)).map
        (pullbackFiniteSetTranslate (alpha := alpha) s I) =
      (finiteSetKernel P I).comp (P s) := by sorry
