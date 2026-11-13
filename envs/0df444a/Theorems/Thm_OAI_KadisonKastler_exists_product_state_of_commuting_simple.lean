-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_product_state_of_commuting_simple
-- name    : OAI.KadisonKastler.exists_product_state_of_commuting_simple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:42:22.053299+00:00
-- url     : https://prove2.me/theorems/1b202b1e-29b7-4bd2-b50e-eaa9ec649ad3
-- title:
--   OAI.KadisonKastler.exists_product_state_of_commuting_simple: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_product_state_of_commuting_simple` of [lean/OAI/Analysis/KadisonKastler/SimpleCommutingProductState.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/SimpleCommutingProductState.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open NaimarkZFC`):
--
--   ```lean
--   theorem exists_product_state_of_commuting_simple [Nontrivial A]
--       (hA : CStarSimple A) (hB : CStarSimple B)
--       (ι : A →⋆ₐ[ℂ] C) (hι : Function.Injective ι)
--       (κ : B →⋆ₐ[ℂ] C)
--       (hcomm : ∀ a b, Commute (ι a) (κ b))
--       (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ) (hg : IsState g) :
--       ∃ φ : C →L[ℂ] ℂ, IsState φ ∧ ∀ a b, φ (ι a*κ b)=f a*g b
--   ```
--
--   **Definitions.** The statement is written with `OAI.NaimarkZFC.IsState` (definitions bundle `OAIQ075A006` of this split); `OAI.KadisonKastler.CStarSimple` (definitions bundle `Q260K003` of this split).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_strongly_invariant_product_of_simple` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/SimpleCommutingProductState.lean (declaration OAI.KadisonKastler.exists_product_state_of_commuting_simple)

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Definitions.Def_OAIQ075A006
import Definitions.Def_Q260K003

section

attribute [-instance] _root_.OAI.KadisonKastler.rationalCoreModule
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

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem exists_product_state_of_commuting_simple [Nontrivial A]
    (hA : CStarSimple A) (hB : CStarSimple B)
    (ι : A →⋆ₐ[ℂ] C) (hι : Function.Injective ι)
    (κ : B →⋆ₐ[ℂ] C)
    (hcomm : ∀ a b, Commute (ι a) (κ b))
    (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ) (hg : IsState g) :
    ∃ φ : C →L[ℂ] ℂ, IsState φ ∧ ∀ a b, φ (ι a*κ b)=f a*g b := by
  sorry

end

end KadisonKastler

end OAI
end
