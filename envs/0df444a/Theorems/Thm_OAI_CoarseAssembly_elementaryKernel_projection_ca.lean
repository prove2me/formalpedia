-- Prove2me | Theorems.Thm_OAI_CoarseAssembly_elementaryKernel_projection_ca
-- name    : OAI.CoarseAssembly.elementaryKernel_projection_ca
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T10:02:06.695771+00:00
-- url     : https://prove2.me/theorems/1f3008d9-fdec-4e32-862b-d7e2e9e723d1
-- title:
--   OAI.CoarseAssembly.elementaryKernel_projection_ca: intermediate lemma from OpenAI, A counterexample to the coarse Novikov conjecture (result family 307)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to the coarse Novikov conjecture (result family 307)*, OpenAI Math Release, September 23, 2026, result family 307, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoarseAssembly.elementaryKernel_projection` of [lean/OAI/Topology/CoarseAssembly/CongruenceSpectral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/CongruenceSpectral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoarseAssembly`, with `open Congruence`, `open NuclearUltrapower`):
--
--   ```lean
--   theorem elementaryKernel_projection_ca (k : ℕ)
--       (hsurj : Function.Surjective (elementaryReduction k))
--       (x : lp (fun _ : Congruence.Quotient k => H) 2)
--       (hx : x ∈ (elementaryLaplacian (H := H) k).ker) :
--       constantProjection (Congruence.Quotient k) x = x
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.SL` (definitions bundle `OAIQ229C003` of this split); `OAI.CoarseAssembly.constantProjection` (definitions bundle `OAIQ229C019` of this split); `OAI.NuclearUltrapower.SOS.E` (definitions bundle `OAIQ229C032` of this split); `OAI.CoarseAssembly.elementaryLaplacian` and `OAI.CoarseAssembly.elementaryReduction` (definitions bundle `OAIQ229C037` of this split); `OAI.CoarseAssembly.Congruence.Quotient` (the published bundle `Def_CoarseAssembly`).
--
--   **Used by.** The proofs of `OAI_CoarseAssembly_provedKazhdanInput_ca` and `OAI.CoarseAssembly.publishedKazhdanInput_of_elementaryReduction_ca` of this split import it.
-- source:
--   OpenAI, A counterexample to the coarse Novikov conjecture (result family 307), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 307; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoarseAssembly.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/CoarseAssembly/CongruenceSpectral.lean (declaration OAI.CoarseAssembly.elementaryKernel_projection)

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.TransferInstance
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoarseAssembly

open Congruence
open NuclearUltrapower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem elementaryKernel_projection_ca (k : ℕ)
    (hsurj : Function.Surjective (elementaryReduction k))
    (x : lp (fun _ : Congruence.Quotient k => H) 2)
    (hx : x ∈ (elementaryLaplacian (H := H) k).ker) :
    constantProjection (Congruence.Quotient k) x = x := by
  sorry

end CoarseAssembly

end

end OAI
end
