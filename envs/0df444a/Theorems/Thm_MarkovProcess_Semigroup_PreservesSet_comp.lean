-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_PreservesSet_comp
-- name    : MarkovProcess.Semigroup.PreservesSet.comp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:16.800031+00:00
-- url     : https://prove2.me/theorems/a8130cf7-3231-4af8-b0fd-821f97f0dab7
-- title:
--   MarkovProcess: comp
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

open Filter Set Topology

noncomputable section

namespace MarkovProcess.Semigroup



namespace PreservesSet

variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}







end PreservesSet

end MarkovProcess.Semigroup

namespace Convex

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end Convex

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



section CompleteSpace

variable [CompleteSpace E]





end CompleteSpace

end ContractiveResolvent

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.PreservesSet
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Invariant sets and strong semigroup limits

This file isolates the topological part of transferring an invariant set from
bounded Yosida approximations to the generated semigroup.  It also records the
finite-iterate consequence of invariance under a normalized resolvent.  The
Poisson-series argument transferring the latter invariance to each exponential
approximant is in `Semigroup/PoissonInvariant.lean`.
-/

open Filter Set Topology






variable {E F G : Type*} {C : Set E} {D : Set F} {K : Set G}



open MarkovProcess.Semigroup.PreservesSet in

theorem MarkovProcess.Semigroup.PreservesSet.comp {S : F → G} {T : E → F}
    (hS : PreservesSet S D K) (hT : PreservesSet T C D) :
    PreservesSet (S ∘ T) C K := by sorry
