-- Prove2me | Theorems.Thm_GlobalTheory_BorelCoh_exists_equivariant_proj_of_irreducible_family
-- name    : GlobalTheory.BorelCoh.exists_equivariant_proj_of_irreducible_family
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:52.126559+00:00
-- url     : https://prove2.me/theorems/8c4731af-c483-4634-9ac1-e64dd221170f
-- title:
--   Borel Coh: exists equivariant proj of irreducible family
-- statement:
--   The Borel Coh construction uses the exists equivariant proj of irreducible family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/PositivityTheory/AutomorphicForms/PublishedInputs/BorelInjectivity/EquivariantProjections/ExistsEquivariantProjOfLeSumIrreducible.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/PositivityTheory/AutomorphicForms/PublishedInputs/BorelInjectivity/EquivariantProjections/ExistsEquivariantProjOfLeSumIrreducible.lean#L68-L75

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

theorem GlobalTheory.BorelCoh.exists_equivariant_proj_of_irreducible_family : ∀ (M O ι : Type) [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] (act : O → Module.End ℂ M) (V : ι → Submodule ℂ M), (∀ i o, ∀ x ∈ V i, act o x ∈ V i) → (∀ i, V i ≠ ⊥) → (∀ i (W : Submodule ℂ M), W ≤ V i → (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V i) → (∀ i j, i ≠ j → ∀ f : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ V i, f (act o x) = act o (f x)) → (∀ x ∈ V i, f x ∈ V j) → ∀ x ∈ V i, f x = 0) → ∀ i, ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧ (∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p x ∈ V i) ∧ (∀ x ∈ V i, p x = x) ∧ ∀ j, j ≠ i → ∀ x ∈ V j, p x = 0 := by sorry
