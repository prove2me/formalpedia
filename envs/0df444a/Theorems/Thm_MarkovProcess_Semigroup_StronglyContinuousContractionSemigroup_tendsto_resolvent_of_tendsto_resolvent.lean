-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_tendsto_resolvent_of_tendsto_resolvent
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_resolvent_of_tendsto_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:32:02.186001+00:00
-- url     : https://prove2.me/theorems/df9364ce-8502-42bf-8387-e516af7f3cae
-- title:
--   MarkovProcess: tendsto_resolvent_of_tendsto_resolvent
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The Trotter--Kato theorem

Let `S i` be a family of strongly continuous contraction semigroups on a Banach space, indexed
along a filter, and let `S'` be one more such semigroup.  Convergence of the semigroups and
convergence of their resolvents are equivalent:

* if the resolvents converge strongly at **one** positive shift `μ`, then the semigroups converge
  strongly, uniformly on every bounded interval of times
  (`tendstoUniformlyOn_operator_of_tendsto_resolvent`, `tendsto_operator_of_tendsto_resolvent`);
* conversely, if the orbits converge at every time, then the resolvents converge at every positive
  shift (`tendsto_resolvent_of_tendsto_operator`), by dominated convergence in the Laplace
  transform that defines the resolvent.

The first implication is proved on the range of the twofold resolvent `R'_μ ∘ R'_μ`, which is
dense (`denseRange_resolvent_resolvent`): there the comparison identity of
`Semigroup/ResolventComparison.lean` expresses the difference of the two orbits through the
difference of the two resolvents evaluated along a compact piece of one fixed orbit, where
equibounded strong convergence is uniform (`Semigroup/CompactStrongConvergence.lean`).  The
contraction bound then transports the conclusion from the dense set to the whole space, uniformly
in the time.

Main results: `denseRange_resolvent_resolvent`,
`tendstoUniformlyOn_operator_of_tendsto_resolvent`, `tendsto_operator_of_tendsto_resolvent`,
`tendsto_resolvent_of_tendsto_operator`, `tendsto_resolvent_of_tendsto_resolvent`.

The converse implication, and the transfer of resolvent convergence from one shift to every
shift that goes through it (`tendsto_resolvent_of_tendsto_resolvent`), read the limit under an
integral and therefore assume the index filter countably generated; the direct implication
assumes nothing about the filter.  This is the same-space Trotter--Kato theorem; the version for
semigroups on a sequence of different spaces (Trotter--Kurtz) is not stated.  Nothing is asserted
about convergence in the operator norm, nor about families that are merely uniformly bounded
rather than contractive.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} {l : Filter ι}















end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The Trotter--Kato theorem

Let `S i` be a family of strongly continuous contraction semigroups on a Banach space, indexed
along a filter, and let `S'` be one more such semigroup.  Convergence of the semigroups and
convergence of their resolvents are equivalent:

* if the resolvents converge strongly at **one** positive shift `μ`, then the semigroups converge
  strongly, uniformly on every bounded interval of times
  (`tendstoUniformlyOn_operator_of_tendsto_resolvent`, `tendsto_operator_of_tendsto_resolvent`);
* conversely, if the orbits converge at every time, then the resolvents converge at every positive
  shift (`tendsto_resolvent_of_tendsto_operator`), by dominated convergence in the Laplace
  transform that defines the resolvent.

The first implication is proved on the range of the twofold resolvent `R'_μ ∘ R'_μ`, which is
dense (`denseRange_resolvent_resolvent`): there the comparison identity of
`Semigroup/ResolventComparison.lean` expresses the difference of the two orbits through the
difference of the two resolvents evaluated along a compact piece of one fixed orbit, where
equibounded strong convergence is uniform (`Semigroup/CompactStrongConvergence.lean`).  The
contraction bound then transports the conclusion from the dense set to the whole space, uniformly
in the time.

Main results: `denseRange_resolvent_resolvent`,
`tendstoUniformlyOn_operator_of_tendsto_resolvent`, `tendsto_operator_of_tendsto_resolvent`,
`tendsto_resolvent_of_tendsto_operator`, `tendsto_resolvent_of_tendsto_resolvent`.

The converse implication, and the transfer of resolvent convergence from one shift to every
shift that goes through it (`tendsto_resolvent_of_tendsto_resolvent`), read the limit under an
integral and therefore assume the index filter countably generated; the direct implication
assumes nothing about the filter.  This is the same-space Trotter--Kato theorem; the version for
semigroups on a sequence of different spaces (Trotter--Kurtz) is not stated.  Nothing is asserted
about convergence in the operator norm, nor about families that are merely uniformly bounded
rather than contractive.
-/

open Filter MeasureTheory Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} {l : Filter ι}













open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup in

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_resolvent_of_tendsto_resolvent [l.IsCountablyGenerated]
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {μ : PositiveShift}
    (hres : ∀ y : E, Tendsto (fun i ↦ (S i).resolvent μ y) l (𝓝 (S'.resolvent μ y)))
    (ν : PositiveShift) (x : E) :
    Tendsto (fun i ↦ (S i).resolvent ν x) l (𝓝 (S'.resolvent ν x)) := by sorry
