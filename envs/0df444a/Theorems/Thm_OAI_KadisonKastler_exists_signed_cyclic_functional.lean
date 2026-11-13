-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_signed_cyclic_functional
-- name    : OAI.KadisonKastler.exists_signed_cyclic_functional
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:37:28.060612+00:00
-- url     : https://prove2.me/theorems/89aad38d-2da6-42ff-ba8c-80b04a61906f
-- title:
--   OAI.KadisonKastler.exists_signed_cyclic_functional: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_signed_cyclic_functional` of [lean/OAI/Analysis/KadisonKastler/SignedCyclicFunctional.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/SignedCyclicFunctional.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open scoped InnerProductSpace`):
--
--   ```lean
--   theorem exists_signed_cyclic_functional (f : A →L[ℂ] ℂ)
--       (hf : ∀ a, f (star a) = star (f a)) (hfn : ‖f‖ = 1) :
--       ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
--         (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (S : H →L[ℂ] H),
--         ‖ξ‖ = 1 ∧ DenseRange (fun a : A => π a ξ) ∧
--         IsSelfAdjoint S ∧ S * S = 1 ∧
--         (∀ a, Commute S (π a)) ∧ ∀ a, f a = inner ℂ (S ξ) (π a ξ)
--   ```
--
--   **Used by.** The proofs of `OAI_KadisonKastler_antiStar_derivation_inner_of_simple` and `OAI.KadisonKastler.publishedSimpleDerivationInner` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/SignedCyclicFunctional.lean (declaration OAI.KadisonKastler.exists_signed_cyclic_functional)

import Mathlib
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Zorn
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

theorem exists_signed_cyclic_functional (f : A →L[ℂ] ℂ)
    (hf : ∀ a, f (star a) = star (f a)) (hfn : ‖f‖ = 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (S : H →L[ℂ] H),
      ‖ξ‖ = 1 ∧ DenseRange (fun a : A => π a ξ) ∧
      IsSelfAdjoint S ∧ S * S = 1 ∧
      (∀ a, Commute S (π a)) ∧ ∀ a, f a = inner ℂ (S ξ) (π a ξ) := by
  sorry

end

end KadisonKastler

end OAI
end
