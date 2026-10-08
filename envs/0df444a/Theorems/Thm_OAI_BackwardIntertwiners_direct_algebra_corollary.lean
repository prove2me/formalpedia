-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_direct_algebra_corollary
-- name    : OAI.BackwardIntertwiners.direct_algebra_corollary
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:22.40876+00:00
-- url     : https://prove2.me/theorems/7d0ea78d-2f5b-40da-9b13-770941e12119
-- statement:
--   The theorem states that on every infinite-dimensional separable complex Hilbert space H there exists a nonzero bounded complex-linear operator T such that ‖Tⁿ‖^(1/n) tends to zero as n tends to infinity through natural numbers. Its commutant, the complex algebra of all bounded complex-linear operators A satisfying AT = TA, is transitive: every closed complex-linear subspace K of H that is invariant under every such A is either {0} or all of H. Moreover, this commutant is a proper subalgebra of the algebra of all bounded complex-linear operators on H, and it is closed in the strong operator topology, namely the topology of pointwise norm convergence on H.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BackwardIntertwiners.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BackwardIntertwiners.lean; bytes 1120..1361
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BackwardIntertwiners

namespace OAI

namespace BackwardIntertwiners

open Filter Topology MeasureTheory Set

noncomputable section

open scoped ENNReal

theorem direct_algebra_corollary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] (hInf : ¬FiniteDimensional ℂ H) :
    Hyperinvariant233.FullClaim (H:=H) := by
  sorry

end
end BackwardIntertwiners
end OAI
