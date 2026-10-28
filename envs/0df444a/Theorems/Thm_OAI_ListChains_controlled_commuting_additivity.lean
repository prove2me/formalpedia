-- Prove2me | Theorems.Thm_OAI_ListChains_controlled_commuting_additivity
-- name    : OAI.ListChains.controlled_commuting_additivity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T02:28:38.806632+00:00
-- url     : https://prove2.me/theorems/4df328b4-add4-4124-9fdb-deebdbce4593
-- title:
--   OAI.ListChains.controlled_commuting_additivity: intermediate lemma from OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ListChains.controlled_commuting_additivity` of [lean/OAI/GroupTheory/FiniteType/ListChainsMapChainComp.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ListChainsMapChainComp.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ListChains`):
--
--   ```lean
--   theorem controlled_commuting_additivity (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
--       {n : ℕ} (hn : 0 < n) {A C : Set G} (hA : IsBound G A) (hC : IsBound G C)
--       (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
--       (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
--       (hJcontrol : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G C)
--       (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
--         boundary G (J c) + J (boundary G c) = mapChain G f c - K G 1 c)
--       (h₁ h₂ : G →* G) (comm : ∀ x y, Commute (h₁ x) (h₂ y)) :
--       ∃ B : Set G, IsBound G B ∧
--         ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
--           FillsAt G B n (mapChain G (fun x => h₁ (f x) * h₂ (f x)) z -
--             mapChain G (h₁ ∘ f) z - mapChain G (h₂ ∘ f) z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ListChains.Chain`, `OAI.ListChains.IsBound`, `OAI.ListChains.K`, `OAI.ListChains.Simplex`, `OAI.ListChains.boundary`, `OAI.ListChains.controlledModule`, `OAI.ListChains.degreeModule` and `OAI.ListChains.mapChain` (definitions bundle `OAIQ66So006` of this split); `OAI.ListChains.FillsAt` (definitions bundle `OAIQ66So013` of this split).
--
--   **Used by.** The proof of `OAI.ListChains.uniform_fillings_from_partial_homotopy` of this split imports it.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ListChainsMapChainComp.lean (declaration OAI.ListChains.controlled_commuting_additivity)

import Mathlib
import Definitions.Def_OAIQ66So013

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

variable (G : Type*)

variable [Group G]

theorem controlled_commuting_additivity (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
    {n : ℕ} (hn : 0 < n) {A C : Set G} (hA : IsBound G A) (hC : IsBound G C)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
    (hJcontrol : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G C)
    (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
      boundary G (J c) + J (boundary G c) = mapChain G f c - K G 1 c)
    (h₁ h₂ : G →* G) (comm : ∀ x y, Commute (h₁ x) (h₂ y)) :
    ∃ B : Set G, IsBound G B ∧
      ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
        FillsAt G B n (mapChain G (fun x => h₁ (f x) * h₂ (f x)) z -
          mapChain G (h₁ ∘ f) z - mapChain G (h₂ ∘ f) z) := by
  sorry

open scoped Pointwise

end

end ListChains

end

end OAI
end
