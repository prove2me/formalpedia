-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialWordFormula_automorphism_word
-- name    : OAI.KadisonSimilarity.TracialWordFormula.automorphism_word
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-13T04:48:31.361962+00:00
-- url     : https://prove2.me/theorems/3df2cfde-4044-41a8-b1cb-afe70e3b8d49
-- title:
--   OAI.KadisonSimilarity.TracialWordFormula.automorphism_word: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialWordFormula.automorphism_word` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialAutomorphismWords.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialAutomorphismWords.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialWordFormula`, with `open TracialCornerGeometry`):
--
--   ```lean
--   theorem automorphism_word (hU : TracialWordFormula G A D U)
--       (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
--       (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
--       G.automorphismUnitary θ hθ
--         (U.inclusion n (tracialWordTensor G A D n d b a c ha hc)) =
--       U.inclusion n (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap
--         (tracialWordTensor G A D n d b a c ha hc))
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.HilbertTensor`, `OAI.KadisonSimilarity.OrthogonalWordLevels`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace`, `OAI.KadisonSimilarity.TensorWordSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.matrixConjugateLetter` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.EndpointTensor` (definitions bundle `OAIQ075A009` of this split); `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.hilbertTensorLift`, `OAI.KadisonSimilarity.tracialWordTensor`, `OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.TracialWordFormula` (definitions bundle `OAIQ075A024` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.baseMatrixWordAction`, `OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityInnerFamily` and `OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityNormedFamily` (definitions bundle `OAIQ075A029` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialAutomorphismWords.lean (declaration OAI.KadisonSimilarity.TracialWordFormula.automorphism_word)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
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
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_OAIQ075A029

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialWordFormula

open TracialCornerGeometry

variable {G : TracialCornerGeometry P H} {A D : StarSubalgebra ℂ P}
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (θ : P ≃⋆ₐ[ℂ] P) (hθ : ∀ x, G.trace (θ x) = G.trace x)
  (hA : ∀ a : A, θ (a : P) = (a : P))
  (hD : ∀ d : D, θ (d : P) = (matrixConjugateLetter D ι u d : P))

attribute [local instance] OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityInnerFamily
variable
  {U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H}

include hA hD in
theorem automorphism_word (hU : TracialWordFormula G A D U)
    (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    G.automorphismUnitary θ hθ
      (U.inclusion n (tracialWordTensor G A D n d b a c ha hc)) =
    U.inclusion n (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap
      (tracialWordTensor G A D n d b a c ha hc)) := by
  sorry

end TracialWordFormula
end KadisonSimilarity

end

end OAI
end
