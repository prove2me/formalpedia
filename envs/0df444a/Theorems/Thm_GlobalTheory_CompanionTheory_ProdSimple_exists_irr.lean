-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_exists_irr
-- name    : GlobalTheory.CompanionTheory.ProdSimple.exists_irr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:34.045839+00:00
-- url     : https://prove2.me/theorems/a0f76181-2851-429b-a21d-87f502e28bd8
-- title:
--   Prod Simple: exists irr
-- statement:
--   The Prod Simple construction uses the exists irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L30-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L30-L98

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

theorem GlobalTheory.CompanionTheory.ProdSimple.exists_irr {Γ : Type} [Group Γ] [Fintype Γ] {W : Type} [AddCommGroup W] [Module ℂ W]
    (T : MonoidAlgebra ℂ Γ →ₗ[ℂ] W) (hT : T 1 ≠ 0) :
    ∃ (N : Submodule ℂ (MonoidAlgebra ℂ Γ))
      (h : ∀ g : Γ, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
      IsIrr (regSub N h) ∧ ∃ n ∈ N, T n ≠ 0 := by sorry
