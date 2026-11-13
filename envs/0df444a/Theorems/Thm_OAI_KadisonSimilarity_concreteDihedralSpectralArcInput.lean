-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_concreteDihedralSpectralArcInput
-- name    : OAI.KadisonSimilarity.concreteDihedralSpectralArcInput
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:42:12.986067+00:00
-- url     : https://prove2.me/theorems/c905c06e-33d1-41ee-939b-148e6eb4c31c
-- title:
--   OAI.KadisonSimilarity.concreteDihedralSpectralArcInput: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.concreteDihedralSpectralArcInput` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/ConcreteDihedralSpectralArc.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/ConcreteDihedralSpectralArc.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open scoped ComplexOrder`):
--
--   ```lean
--   theorem concreteDihedralSpectralArcInput (Ω : H) (P : VonNeumannAlgebra H)
--       (w d : (H →L[ℂ] H)ˣ) (hwP : (w : H →L[ℂ] H) ∈ P)
--       (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
--       (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
--       (hd : (d : H →L[ℂ] H) * (d : H →L[ℂ] H) = 1)
--       (hds : star (d : H →L[ℂ] H) = (d : H →L[ℂ] H))
--       (hconj : (d : H →L[ℂ] H) * (w : H →L[ℂ] H) =
--         star (w : H →L[ℂ] H) * (d : H →L[ℂ] H))
--       (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
--       (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * (d : H →L[ℂ] H)) = 0) :
--       DihedralSpectralArcInput (vectorTrace Ω).toLinearMap P.toStarSubalgebra w d
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.vectorTrace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.DihedralSpectralArcInput` (definitions bundle `OAIQ075A010` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/ConcreteDihedralSpectralArc.lean (declaration OAI.KadisonSimilarity.concreteDihedralSpectralArcInput)

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RealImaginaryPart
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
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.UniformConvergence
import Definitions.Def_OAIQ075A010

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem concreteDihedralSpectralArcInput (Ω : H) (P : VonNeumannAlgebra H)
    (w d : (H →L[ℂ] H)ˣ) (hwP : (w : H →L[ℂ] H) ∈ P)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hd : (d : H →L[ℂ] H) * (d : H →L[ℂ] H) = 1)
    (hds : star (d : H →L[ℂ] H) = (d : H →L[ℂ] H))
    (hconj : (d : H →L[ℂ] H) * (w : H →L[ℂ] H) =
      star (w : H →L[ℂ] H) * (d : H →L[ℂ] H))
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * (d : H →L[ℂ] H)) = 0) :
    DihedralSpectralArcInput (vectorTrace Ω).toLinearMap P.toStarSubalgebra w d := by
  sorry

end KadisonSimilarity

end

end OAI
end
