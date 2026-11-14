-- Prove2me | Theorems.Thm_OAI_KadisonKastler_mem_commutant_of_commutes_projections
-- name    : OAI.KadisonKastler.mem_commutant_of_commutes_projections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:31.70466+00:00
-- url     : https://prove2.me/theorems/100d4cfc-8894-45ac-ab17-f43dfda1ecc7
-- title:
--   OAI.KadisonKastler.mem_commutant_of_commutes_projections: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.mem_commutant_of_commutes_projections` of [lean/OAI/Analysis/KadisonKastler/VonNeumannProjectionCommutation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/VonNeumannProjectionCommutation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open Generator.Tracial`, `open scoped ComplexStarModule`):
--
--   ```lean
--   theorem mem_commutant_of_commutes_projections (N : VonNeumannAlgebra H)
--       (C : H →L[ℂ] H) (hp : ∀ p : AlgebraProjection N, Commute C p.val.val) :
--       C ∈ N.commutant
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.AlgebraProjection` (definitions bundle `OAIQ075A003` of this split).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_selfAdjoint_split_of_factor_commutant` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/VonNeumannProjectionCommutation.lean (declaration OAI.KadisonKastler.mem_commutant_of_commutes_projections)

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Sequences
import Definitions.Def_OAIQ075A003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem mem_commutant_of_commutes_projections (N : VonNeumannAlgebra H)
    (C : H →L[ℂ] H) (hp : ∀ p : AlgebraProjection N, Commute C p.val.val) :
    C ∈ N.commutant := by
  sorry

end

end KadisonKastler

end OAI
end
