-- Prove2me | Theorems.Thm_OAI_TwistedBrin_Basis_pair_regular_products
-- name    : OAI.TwistedBrin.Basis.pair_regular_products
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:38:19.07248+00:00
-- url     : https://prove2.me/theorems/d24663f0-fa91-4f84-b92e-d21b8fbb7446
-- title:
--   OAI.TwistedBrin.Basis.pair_regular_products: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TwistedBrin.Basis.pair_regular_products` of [lean/OAI/GroupTheory/FiniteType/FiniteIndexProducts.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/FiniteIndexProducts.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TwistedBrin.Basis`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`):
--
--   ```lean
--   lemma pair_regular_products (hρ : Function.Injective ρ)
--       (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
--       (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
--         IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1)))
--       {B C : Basis ρ} (hBC : CutRefines ρ B C) (I : Type) (n : ℕ) :
--       IsZero (groupHomology (RegularProductR.rep ℤ (pairStabilizer ρ B C) I) (n+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RegularProductR.rep` (definitions bundle `OAIQ66So003` of this split); `OAI.TwistedBrin.pointwiseStabilizer` (definitions bundle `OAIQ66So009` of this split); `OAI.TwistedBrin.Basis`, `OAI.TwistedBrin.Box`, `OAI.TwistedBrin.localGroup` and `OAI.TwistedBrin.Basis.CutRefines` (definitions bundle `OAIQ66So015` of this split); `OAI.TwistedBrin.Basis.pairStabilizer` (definitions bundle `OAIQ66So021` of this split).
--
--   **Used by.** The proof of `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/FiniteIndexProducts.lean (declaration OAI.TwistedBrin.Basis.pair_regular_products)

import Mathlib
import Definitions.Def_OAIQ66So021

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

namespace TwistedBrin.Basis
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

lemma pair_regular_products (hρ : Function.Injective ρ)
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1)))
    {B C : Basis ρ} (hBC : CutRefines ρ B C) (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (pairStabilizer ρ B C) I) (n+1)) := by
  sorry
end TwistedBrin.Basis

end

end OAI
end
