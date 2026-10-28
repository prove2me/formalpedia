-- Prove2me | Theorems.Thm_OAI_SimpleFInftyOvergroups_SplittingTorusModel_products
-- name    : OAI.SimpleFInftyOvergroups.SplittingTorusModel.products
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:40:50.458751+00:00
-- url     : https://prove2.me/theorems/07e5d4da-ba41-4ed5-bea4-5036afedae78
-- title:
--   OAI.SimpleFInftyOvergroups.SplittingTorusModel.products: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SimpleFInftyOvergroups.SplittingTorusModel.products` of [lean/OAI/GroupTheory/FiniteType/OrderChainsExactSubtypeOfExactSet.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/OrderChainsExactSubtypeOfExactSet.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SimpleFInftyOvergroups.SplittingTorusModel`, with `open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits`):
--
--   ```lean
--   theorem products (M : SplittingTorusModel G) (I : Type) (n : ℕ) :
--       IsZero (groupHomology (RegularProductR.rep ℤ G I) (n+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RegularProductR.rep` (definitions bundle `OAIQ66So003` of this split); `OAI.SimpleFInftyOvergroups.SplittingTorusModel` (definitions bundle `OAIQ66So026` of this split).
--
--   **Used by.** The proofs of `OAI.StageGeometry.localGroup_geometric_of_binary_ring_data` and `OAI_TwistedBrin_localGroup_geometric_of_torus_models` of this split import it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/OrderChainsExactSubtypeOfExactSet.lean (declaration OAI.SimpleFInftyOvergroups.SplittingTorusModel.products)

import Mathlib
import Definitions.Def_OAIQ66So026

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SimpleFInftyOvergroups.SplittingTorusModel
variable {G : Type} [Group G]

theorem products (M : SplittingTorusModel G) (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) (n+1)) := by
  sorry
end SimpleFInftyOvergroups.SplittingTorusModel

end
end

end OAI
end
