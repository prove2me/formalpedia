-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_exists_tracially_symmetrized
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.exists_tracially_symmetrized
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:48:28.168805+00:00
-- url     : https://prove2.me/theorems/478bddaf-6430-4030-aa50-bf9d3ee950b6
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.exists_tracially_symmetrized: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.exists_tracially_symmetrized` of [lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialMatrixSymmetrization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialMatrixSymmetrization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`, with `open MeasureTheory TopologicalSpace`, `open scoped Topology CStarAlgebra ComplexOrder`):
--
--   ```lean
--   theorem exists_tracially_symmetrized (T : H →L[ℂ] H)
--       (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
--       {t ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
--       ∃ Y : H →L[ℂ] H,
--         ‖Y‖ ≤ ‖T‖ ∧
--         (∀ d : D, Y.comp (G.left (d : P)) = (G.left (d : P)).comp Y) ∧
--         (∀ j w, Y.comp
--             (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
--           (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y) ∧
--         G.TraceCornerBound D Y t ε ∧ G.baseOperator A Y = G.baseOperator A T
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.NestedTracialMatrices` and `OAI.KadisonSimilarity.TracialCornerGeometry` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.MatrixConjugationExtensionInput` (definitions bundle `OAIQ075A023` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.TraceCornerBound` (definitions bundle `OAIQ075A028` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.tracialMatrixUnitaryRepresentation` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/Tracial/TracialMatrixSymmetrization.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.exists_tracially_symmetrized)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

namespace TracialCornerGeometry

open MeasureTheory TopologicalSpace
open scoped Topology CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)

include hgen hfaithful in
theorem exists_tracially_symmetrized (T : H →L[ℂ] H)
    (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
    {t ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ∃ Y : H →L[ℂ] H,
      ‖Y‖ ≤ ‖T‖ ∧
      (∀ d : D, Y.comp (G.left (d : P)) = (G.left (d : P)).comp Y) ∧
      (∀ j w, Y.comp
          (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y) ∧
      G.TraceCornerBound D Y t ε ∧ G.baseOperator A Y = G.baseOperator A T := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
