-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_cyclic_derivation_implementation_of_column_tests
-- name    : OAI.KadisonSimilarity.cyclic_derivation_implementation_of_column_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:45:28.028741+00:00
-- url     : https://prove2.me/theorems/a5a8b5a4-9b4d-424e-92ee-2a2a3ba6996e
-- title:
--   OAI.KadisonSimilarity.cyclic_derivation_implementation_of_column_tests: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.cyclic_derivation_implementation_of_column_tests` of [lean/OAI/Analysis/KadisonSimilarity/Derivation/CyclicColumnTests.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/Derivation/CyclicColumnTests.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open Filter`, `open scoped ComplexOrder Topology`):
--
--   ```lean
--   theorem cyclic_derivation_implementation_of_column_tests
--       {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
--       (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
--       (δ : A →L[ℂ] (K →L[ℂ] F))
--       (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
--       (htests : CyclicColumnTests σ)
--       (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
--       ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
--         ‖V‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.RectangularSum` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.CyclicColumnTests` (definitions bundle `OAIQ075A010` of this split); `OAI.KadisonSimilarity.PaulsenSimilarityInput` (definitions bundle `OAIQ075A017` of this split); `OAI.KadisonSimilarity.normalizedRectangularRepresentation` (definitions bundle `OAIQ075A018` of this split).
--
--   **Used by.** The proofs of `OAI_KadisonKastler_cyclic_spatial_derivation` and `OAI.KadisonKastler.exists_simple_spatial_derivation` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/Derivation/CyclicColumnTests.lean (declaration OAI.KadisonSimilarity.cyclic_derivation_implementation_of_column_tests)

import Mathlib
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_OAIQ075A017
import Definitions.Def_OAIQ075A018

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ComplexOrder Topology

variable {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem cyclic_derivation_implementation_of_column_tests
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (htests : CyclicColumnTests σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ := by
  sorry

end KadisonSimilarity

end

end OAI
end
