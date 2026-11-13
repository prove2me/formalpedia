-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_centeredDihedralArc_rotation_moment
-- name    : OAI.KadisonSimilarity.centeredDihedralArc_rotation_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:41:30.733198+00:00
-- url     : https://prove2.me/theorems/2f005848-437a-4665-b248-2240d9191f9e
-- title:
--   OAI.KadisonSimilarity.centeredDihedralArc_rotation_moment: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.centeredDihedralArc_rotation_moment` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/ConcreteDihedralSpectralArc.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/ConcreteDihedralSpectralArc.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`, with `open scoped ComplexOrder`):
--
--   ```lean
--   theorem centeredDihedralArc_rotation_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
--       (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
--       (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
--       (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
--       {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (l : ℤ) :
--       vectorTrace Ω (centeredDihedralArc (w : H →L[ℂ] H) θ * (↑(w ^ l) : H →L[ℂ] H)) =
--         arcFourierIntegral θ l
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.arcFourierIntegral` and `OAI.KadisonSimilarity.vectorTrace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.centeredDihedralArc` (definitions bundle `OAIQ075A006` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.concreteDihedralSpectralArcInput` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/ConcreteDihedralSpectralArc.lean (declaration OAI.KadisonSimilarity.centeredDihedralArc_rotation_moment)

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
import Definitions.Def_OAIQ075A004
import Definitions.Def_OAIQ075A006

section

attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centeredDihedralArc_rotation_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (l : ℤ) :
    vectorTrace Ω (centeredDihedralArc (w : H →L[ℂ] H) θ * (↑(w ^ l) : H →L[ℂ] H)) =
      arcFourierIntegral θ l := by
  sorry

end KadisonSimilarity

end

end OAI
end
