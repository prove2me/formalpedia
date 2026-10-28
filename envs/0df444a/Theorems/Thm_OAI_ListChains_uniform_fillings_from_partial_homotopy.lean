-- Prove2me | Theorems.Thm_OAI_ListChains_uniform_fillings_from_partial_homotopy
-- name    : OAI.ListChains.uniform_fillings_from_partial_homotopy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:36:54.303437+00:00
-- url     : https://prove2.me/theorems/5d479d86-0dff-410f-8522-736e1e4daf03
-- title:
--   OAI.ListChains.uniform_fillings_from_partial_homotopy: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ListChains.uniform_fillings_from_partial_homotopy` of [lean/OAI/GroupTheory/FiniteType/BinaryPrefixOperators.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/BinaryPrefixOperators.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ListChains`):
--
--   ```lean
--   theorem uniform_fillings_from_partial_homotopy
--       {f g : G →* G} (F₂ : IdempotentSplittings G (ZMod 2) f)
--       (F₃ : IdempotentSplittings G (ZMod 3) f)
--       {A : Set G} (hA : IsBound G A) {n : ℕ} (hn : 0 < n)
--       (H : ControlledNullBelow G g A n) :
--       ∃ B : Set G, IsBound G B ∧ ∀ z, z ∈ degreeModule G n →
--         z ∈ controlledModule G A → boundary G z = 0 →
--         FillsAt G B n (mapChain G (f ∘ g) z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ListChains.Chain`, `OAI.ListChains.IsBound`, `OAI.ListChains.Simplex`, `OAI.ListChains.boundary`, `OAI.ListChains.controlledModule`, `OAI.ListChains.degreeModule` and `OAI.ListChains.mapChain` (definitions bundle `OAIQ66So006` of this split); `OAI.ListChains.ControlledNullBelow` and `OAI.ListChains.FillsAt` (definitions bundle `OAIQ66So013` of this split); `OAI.ListChains.IdempotentSplittings` (definitions bundle `OAIQ66So019` of this split).
--
--   **Used by.** The proof of `OAI.SimpleFInftyOvergroups.SplittingTorusModel.products` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/BinaryPrefixOperators.lean (declaration OAI.ListChains.uniform_fillings_from_partial_homotopy)

import Mathlib
import Definitions.Def_OAIQ66So019

section

attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G : Type*) [Group G]

theorem uniform_fillings_from_partial_homotopy
    {f g : G →* G} (F₂ : IdempotentSplittings G (ZMod 2) f)
    (F₃ : IdempotentSplittings G (ZMod 3) f)
    {A : Set G} (hA : IsBound G A) {n : ℕ} (hn : 0 < n)
    (H : ControlledNullBelow G g A n) :
    ∃ B : Set G, IsBound G B ∧ ∀ z, z ∈ degreeModule G n →
      z ∈ controlledModule G A → boundary G z = 0 →
      FillsAt G B n (mapChain G (f ∘ g) z) := by
  sorry

end

end ListChains

end

end OAI
end
