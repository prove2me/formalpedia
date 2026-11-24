-- Prove2me | Theorems.Thm_GlobalTheory_BorelCoh_exists_equivariant_proj_of_le_sum_irreducible
-- name    : GlobalTheory.BorelCoh.exists_equivariant_proj_of_le_sum_irreducible
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:01:44.250335+00:00
-- url     : https://prove2.me/theorems/302ebe21-f1f2-486f-b051-3c341c1defba
-- title:
--   Borel Coh: exists equivariant proj of le sum irreducible
-- statement:
--   The Borel Coh construction uses the exists equivariant proj of le sum irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/PositivityTheory/AutomorphicForms/PublishedInputs/BorelInjectivity/EquivariantProjections/ExistsEquivariantProjOfLeSumIrreducible.lean#L7-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/PositivityTheory/AutomorphicForms/PublishedInputs/BorelInjectivity/EquivariantProjections/ExistsEquivariantProjOfLeSumIrreducible.lean#L7-L66

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_BasicForm
import Definitions.Def_PositivityTheory_AutomorphicForms_PublishedInputs_BorelInjectivity_EquivariantProjections_ExistsEquivariantProjOfLeSumIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BorelCoh CategoryTheory
open scoped ContDiff Matrix
open GlobalTheory GlobalTheory.BorelCoh

theorem GlobalTheory.BorelCoh.exists_equivariant_proj_of_le_sum_irreducible {M O : Type} [AddCommGroup M] [Module ℂ M]
    (act : O → Module.End ℂ M) (V : Submodule ℂ M) (hVst : ∀ o, ∀ x ∈ V, act o x ∈ V)
    (hV : V ≤ ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) :
    ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧
      (∀ x, p x ∈ V) ∧ (∀ x ∈ V, p x = x) := by sorry
