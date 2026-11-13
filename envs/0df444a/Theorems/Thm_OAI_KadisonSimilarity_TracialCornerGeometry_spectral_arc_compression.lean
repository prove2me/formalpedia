-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_spectral_arc_compression
-- name    : OAI.KadisonSimilarity.TracialCornerGeometry.spectral_arc_compression
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:44:54.760589+00:00
-- url     : https://prove2.me/theorems/f2976431-f0fa-4ace-bb61-e8b9d515e47c
-- title:
--   OAI.KadisonSimilarity.TracialCornerGeometry.spectral_arc_compression: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.TracialCornerGeometry.spectral_arc_compression` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialSpectralCompression.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialSpectralCompression.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity.TracialCornerGeometry`):
--
--   ```lean
--   theorem spectral_arc_compression
--       (A C D S : StarSubalgebra ℂ P)
--       (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
--       (hCS : C ≤ S) (hDS : D ≤ S)
--       (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
--       (hfreeDA : ScalarFree G.trace D A)
--       (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
--       (hdC : (d : P) ∈ C)
--       (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
--       (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
--       (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
--       (hsstar : star (↑(w⁻¹ * d) : P) = (↑(w⁻¹ * d) : P))
--       (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
--         (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(↑(w⁻¹ * d) : P)}):
--           Set P))).topologicalClosure)
--       (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
--       (hp : IsStarProjection (dihedralHalfProjection d))
--       (hpD : dihedralHalfProjection d ∈ D)
--       (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))
--       (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
--         (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
--         (CStarCorner.subalgebra (dihedralHalfProjection d) hp C
--           (C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2))))
--       (e : CStarCorner (dihedralHalfProjection d) hp)
--       (he : IsStarProjection (e : P)) (heD : (e : P) ∈ D)
--       {N : ℕ} (hN : 0 < N)
--       (F : DihedralSpectralArc G.trace C w d (arcWidth N))
--       (t : ℝ) (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
--       (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
--       (U : Fin N → G.baseSpace A →L[ℂ] H)
--       (hU : ∀ i (a : A), U i (G.baseVector A a) =
--         c • G.vector ((e : P) * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P))) :
--       (sumColumns U).adjoint.comp
--         ((G.left ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))).comp
--           (sumColumns U)) =
--         ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
--           (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
--             ContinuousLinearMap.id ℂ (G.baseSpace A) +
--           (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P))
--   ```
--
--   **Definitions.** The statement is written with `OAI.closedSubmoduleInner`, `OAI.closedSubmoduleNormedAddCommGroup`, `OAI.closedSubmoduleNormedSpace`, `OAI.KadisonSimilarity.CStarCorner`, `OAI.KadisonSimilarity.DihedralSpectralArc`, `OAI.KadisonSimilarity.ScalarFree`, `OAI.KadisonSimilarity.TracialCornerGeometry`, `OAI.KadisonSimilarity.TracialExpectation`, `OAI.KadisonSimilarity.dihedralHalfProjection`, `OAI.KadisonSimilarity.sumColumns`, `OAI.KadisonSimilarity.CStarCorner.instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra`, `OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex`, `OAI.KadisonSimilarity.CStarCorner.normalizedTrace` and `OAI.KadisonSimilarity.CStarCorner.subalgebra` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.arcHankelMatrix`, `OAI.KadisonSimilarity.arcWidth` and `OAI.KadisonSimilarity.realArcFourierCoefficient` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace` and `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector` (definitions bundle `OAIQ075A016` of this split); `OAI.KadisonSimilarity.HilbertCopies` and `OAI.KadisonSimilarity.matrixOperator` (the published bundle `Def_KadisonSimilarity`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/TracialSpectralCompression.lean (declaration OAI.KadisonSimilarity.TracialCornerGeometry.spectral_arc_compression)

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.BilinearMap
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
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A006
import Definitions.Def_OAIQ075A016

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem spectral_arc_compression
    (A C D S : StarSubalgebra ℂ P)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCS : C ≤ S) (hDS : D ≤ S)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (hfreeDA : ScalarFree G.trace D A)
    (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (hdC : (d : P) ∈ C)
    (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
    (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
    (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
    (hsstar : star (↑(w⁻¹ * d) : P) = (↑(w⁻¹ * d) : P))
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(↑(w⁻¹ * d) : P)}):
        Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpD : dihedralHalfProjection d ∈ D)
    (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C
        (C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2))))
    (e : CStarCorner (dihedralHalfProjection d) hp)
    (he : IsStarProjection (e : P)) (heD : (e : P) ∈ D)
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C w d (arcWidth N))
    (t : ℝ) (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → G.baseSpace A →L[ℂ] H)
    (hU : ∀ i (a : A), U i (G.baseVector A a) =
      c • G.vector ((e : P) * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P))) :
    (sumColumns U).adjoint.comp
      ((G.left ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))).comp
        (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P)) := by
  sorry

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end
