-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSupport_exists_generalizedInverse
-- name    : GlobalTheory.CompanionTheory.TyFinSupport.exists_generalizedInverse
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:37.2608+00:00
-- url     : https://prove2.me/theorems/b5984dbb-bc87-49f4-804c-7b29e0bef189
-- title:
--   Ty Fin Support: exists generalized Inverse
-- statement:
--   The Ty Fin Support construction uses the exists generalized Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalSupportExists.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalSupportExists.lean#L12-L24

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

theorem GlobalTheory.CompanionTheory.TyFinSupport.exists_generalizedInverse {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) : ∃ g : W →ₗ[ℂ] V, Φ ∘ₗ g ∘ₗ Φ = Φ := by sorry
