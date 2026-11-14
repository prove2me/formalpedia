-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_nullset_neutral_root_holonomy
-- name    : OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:34:54.404129+00:00
-- url     : https://prove2.me/theorems/add3d2a5-4e93-45d1-a54d-569bbd21e873
-- title:
--   OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/RootHolonomy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/RootHolonomy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set Filter MeasureTheory`, `open scoped Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_nullset_neutral_root_holonomy
--       (d : ℕ) {a b : Fin (d + 1)} (hab : a ≠ b)
--       (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
--       (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b) :
--       ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
--         ∀ x ∉ N, ∀ y ∉ N, ∀ g : G (d + 1), rightAction x g = y → ∀ c : ℝ,
--           Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
--             diagonalOneParameter ell hell (-t)) atTop
--             (𝓝 (Matrix.SpecialLinearGroup.transvection hab c)) →
--           intrinsicRootLeaf hab μ y = basedRealMeasure (intrinsicRootLeaf hab μ x) c
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.basedRealMeasure` and `OAI.PrimeDegreePackets.diagonalOneParameter` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.intrinsicRootLeaf` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.PhysicalPrefixWindow.independent`, `OAI.DukePrimeDegree.exists_nullset_nonparallel_root_constancy` and `OAI.DukePrimeDegree.root_invariant_of_adjacent_nonatomic_leaves` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/RootHolonomy.lean (declaration OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy)

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke022

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_neutral_root_holonomy
    (d : ℕ) {a b : Fin (d + 1)} (hab : a ≠ b)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ y ∉ N, ∀ g : G (d + 1), rightAction x g = y → ∀ c : ℝ,
        Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
          diagonalOneParameter ell hell (-t)) atTop
          (𝓝 (Matrix.SpecialLinearGroup.transvection hab c)) →
        intrinsicRootLeaf hab μ y = basedRealMeasure (intrinsicRootLeaf hab μ x) c := by
  sorry

end DukePrimeDegree

end

end OAI
end
