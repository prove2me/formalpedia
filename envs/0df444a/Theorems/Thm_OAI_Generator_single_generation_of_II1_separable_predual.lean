-- Prove2me | Theorems.Thm_OAI_Generator_single_generation_of_II1_separable_predual
-- name    : OAI.Generator.single_generation_of_II1_separable_predual
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:42.649311+00:00
-- url     : https://prove2.me/theorems/05beabb5-1c0c-48f1-ace0-07e90b07dd0a
-- statement:
--   The theorem states that, for a complex Hilbert space H (complete inner product space) and a star-subalgebra S of the bounded operators on H, if S is a II₁ factor and has separable predual, then S is singly generated. Here IsII1Factor S means: the zero operator differs from the identity (so H is nontrivial); S is closed in the weak operator topology; S has trivial center, so every element of S commuting with all elements of S is a scalar multiple of the identity; S is finite, so every v in S with v*v = 1 also satisfies vv* = 1; and S is diffuse in the sense that every nonzero self-adjoint projection p in S has a nonzero self-adjoint projection q in S, different from p, with pq = q = qp (that is, q lies strictly below p). HasSeparablePredual S means there exist a complex Banach space X, in the same universe as H, that is separable, together with a conjugate-linear isometric equivalence from the strong dual of X onto S. SinglyGenerated S means there is an element x of S such that the smallest weak-operator-closed star-subalgebra of B(H) containing x equals S. The theorem is stated with its proof admitted (sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FactorGeneration.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FactorGeneration.lean; bytes 1523..1708
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Definitions.Def_FactorGeneration

namespace OAI

noncomputable section

namespace Generator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [-instance] instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace

attribute [instance] instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace

theorem single_generation_of_II1_separable_predual
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S)
    (hsep : HasSeparablePredual S) : SinglyGenerated S := by
  sorry

end Generator
end
end OAI
