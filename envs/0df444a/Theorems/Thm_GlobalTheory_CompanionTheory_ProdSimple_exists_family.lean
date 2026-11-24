-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_exists_family
-- name    : GlobalTheory.CompanionTheory.ProdSimple.exists_family
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:30.906265+00:00
-- url     : https://prove2.me/theorems/eef2da92-1038-49d1-b274-2eb6558a6114
-- title:
--   Prod Simple: exists family
-- statement:
--   The Prod Simple construction uses the exists family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L135-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L135-L165

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple
variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.CompanionTheory.ProdSimple.exists_family (ρ : Representation ℂ (∀ c, L c) W) (v : W) (hv : v ≠ 0) :
    ∃ x : ∀ c, MonoidAlgebra ℂ (L c),
      (∀ c, ∃ (N : Submodule ℂ (MonoidAlgebra ℂ (L c)))
        (h : ∀ g : L c, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
        IsIrr (regSub N h) ∧ x c ∈ N) ∧ psi ρ v x ≠ 0 := by sorry
