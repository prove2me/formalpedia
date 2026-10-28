-- Prove2me | Theorems.Thm_OAI_ProductFiniteResolution_finite_free_resolution_of_products
-- name    : OAI.ProductFiniteResolution.finite_free_resolution_of_products
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:13:25.484989+00:00
-- url     : https://prove2.me/theorems/a2eaae78-68a7-4b86-aa6c-222d28ad7f65
-- title:
--   OAI.ProductFiniteResolution.finite_free_resolution_of_products: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ProductFiniteResolution.finite_free_resolution_of_products` of [lean/OAI/GroupTheory/FiniteType/ProductFiniteResolutionBeginningOfComplex.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ProductFiniteResolutionBeginningOfComplex.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ProductFiniteResolution`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory`, `open Classical`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation`, `open scoped MonoidalCategory`, `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`):
--
--   ```lean
--   theorem finite_free_resolution_of_products
--       (hz : ∀ (I : Type) (n : ℕ), 2 ≤ n → IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
--       ∃ P : ProjectiveResolution (Rep.trivial ℤ G ℤ),
--         ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free ℤ G α)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RegularProductR.rep` (definitions bundle `OAIQ66So003` of this split).
--
--   **Used by.** The proofs of `OAI.SimpleFInftyOvergroups.SplittingTorusModel.products`, `OAI_TwistedBrin_Basis_CutBasis_simplex_stabilizer_products` and `OAI.TwistedBrin.Basis.pair_regular_products` of this split import it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ProductFiniteResolutionBeginningOfComplex.lean (declaration OAI.ProductFiniteResolution.finite_free_resolution_of_products)

import Mathlib
import Definitions.Def_OAIQ66So003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

namespace ProductFiniteResolution
variable (G : Type) [Group G] [Group.IsFinitelyPresented G]

theorem finite_free_resolution_of_products
    (hz : ∀ (I : Type) (n : ℕ), 2 ≤ n → IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
    ∃ P : ProjectiveResolution (Rep.trivial ℤ G ℤ),
      ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free ℤ G α) := by
  sorry
end ProductFiniteResolution

namespace OrbitBrown
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end OrbitBrown

end

end OAI
end
