-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSupport_exists_reverse_intertwiner
-- name    : GlobalTheory.CompanionTheory.TyFinSupport.exists_reverse_intertwiner
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:04:28.874439+00:00
-- url     : https://prove2.me/theorems/f5b397e4-f51f-408f-84fa-d8def568cfb6
-- title:
--   Ty Fin Support: exists reverse intertwiner
-- statement:
--   The Ty Fin Support construction uses the exists reverse intertwiner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalSupportExists.lean#L26-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalSupportExists.lean#L26-L62

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalSupportExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSupport

theorem GlobalTheory.CompanionTheory.TyFinSupport.exists_reverse_intertwiner {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (Φ : V →ₗ[ℂ] W) (hΦ : Φ ≠ 0) (h : ∀ p, Φ ∘ₗ ρ p = σ p ∘ₗ Φ) :
    ∃ ψ : W →ₗ[ℂ] V, ψ ≠ 0 ∧ ∀ p, ψ ∘ₗ σ p = ρ p ∘ₗ ψ := by sorry
