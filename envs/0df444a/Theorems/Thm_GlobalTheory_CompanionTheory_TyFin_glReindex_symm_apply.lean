-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_glReindex_symm_apply
-- name    : GlobalTheory.CompanionTheory.TyFin.glReindex_symm_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:48.343068+00:00
-- url     : https://prove2.me/theorems/ea6e9b65-3ece-42cc-bb52-41707ab39a54
-- title:
--   Ty Fin: gl Reindex symm apply
-- statement:
--   The Ty Fin construction uses the gl Reindex symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalIsomorphismProperties.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalIsomorphismProperties.lean#L29-L31

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
omit [Fintype K] [DecidableEq K]

theorem GlobalTheory.CompanionTheory.TyFin.glReindex_symm_apply (e : α ≃ β) (g : GL β K) :
    glReindex K e (glReindex K e.symm g) = g := by sorry
