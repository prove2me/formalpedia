-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_simple_spatial_derivation
-- name    : OAI.KadisonKastler.exists_simple_spatial_derivation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:47:28.483897+00:00
-- url     : https://prove2.me/theorems/6864b567-5d05-4f0c-81f7-aeb5acceae9a
-- title:
--   OAI.KadisonKastler.exists_simple_spatial_derivation: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_simple_spatial_derivation` of [lean/OAI/Analysis/KadisonKastler/CyclicSpatialDerivation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CyclicSpatialDerivation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`):
--
--   ```lean
--   theorem exists_simple_spatial_derivation [Nontrivial A]
--       (hA : CStarSimple A) (D : A →L[ℂ] A)
--       (hD : ∀ x y, D (x * y) = D x * y + x * D y)
--       (hstar : ∀ x, D (star x) = -star (D x)) :
--       ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
--         (_ : CompleteSpace H) (_ : Nontrivial H)
--         (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
--         Function.Injective π ∧ NaimarkZFC.IsIrreducible π.toNonUnitalStarAlgHom ∧
--         ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧
--           ∀ a, π (D a) = T * π a - π a * T
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.CStarSimple` (definitions bundle `Q260K003` of this split); `OAI.NaimarkZFC.IsIrreducible` (definitions bundle `Q260K007` of this split).
--
--   **Used by.** The proofs of `OAI_KadisonKastler_antiStar_derivation_inner_of_simple` and `OAI.KadisonKastler.publishedSimpleDerivationInner` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/CyclicSpatialDerivation.lean (declaration OAI.KadisonKastler.exists_simple_spatial_derivation)

import Mathlib
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Definitions.Def_Q260K003
import Definitions.Def_Q260K007

section

attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_simple_spatial_derivation [Nontrivial A]
    (hA : CStarSimple A) (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : Nontrivial H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ NaimarkZFC.IsIrreducible π.toNonUnitalStarAlgHom ∧
      ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧
        ∀ a, π (D a) = T * π a - π a * T := by
  sorry

end

end KadisonKastler

end OAI
end
