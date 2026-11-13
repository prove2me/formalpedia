-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_invariant_state_preserving_values
-- name    : OAI.KadisonKastler.exists_invariant_state_preserving_values
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T05:00:57.343257+00:00
-- url     : https://prove2.me/theorems/3e281519-6837-4543-abd0-0e577c5f82b9
-- title:
--   OAI.KadisonKastler.exists_invariant_state_preserving_values: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_invariant_state_preserving_values` of [lean/OAI/Analysis/KadisonKastler/InvariantStateExtension.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/InvariantStateExtension.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open NaimarkZFC`):
--
--   ```lean
--   theorem exists_invariant_state_preserving_values
--       (U : G →* unitary (H →L[ℂ] H))
--       (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
--       (A : Set (H →L[ℂ] H))
--       (hA : ∀ T ∈ A, ∀ g : G, φ (unitaryConj (U g) T)=φ T) :
--       ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
--         (∀ (g : G) (T : H →L[ℂ] H), ψ (unitaryConj (U g) T)=ψ T) ∧
--         ∀ T ∈ A, ψ T=φ T
--   ```
--
--   **Definitions.** The statement is written with `OAI.NaimarkZFC.IsState` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonKastler.unitaryConj` (the published bundle `Def_StrongKadisonKastler`).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_strongly_invariant_product_of_simple` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/InvariantStateExtension.lean (declaration OAI.KadisonKastler.exists_invariant_state_preserving_values)

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_OAIQ075A006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_invariant_state_preserving_values
    (U : G →* unitary (H →L[ℂ] H))
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (A : Set (H →L[ℂ] H))
    (hA : ∀ T ∈ A, ∀ g : G, φ (unitaryConj (U g) T)=φ T) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (g : G) (T : H →L[ℂ] H), ψ (unitaryConj (U g) T)=ψ T) ∧
      ∀ T ∈ A, ψ T=φ T := by
  sorry

end

end KadisonKastler

end OAI
end
