-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_glReindex_refl
-- name    : GlobalTheory.CompanionTheory.TyFin.glReindex_refl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:08.286253+00:00
-- url     : https://prove2.me/theorems/800504b7-0268-4651-b037-5627966dce6d
-- title:
--   Ty Fin: gl Reindex refl
-- statement:
--   The Ty Fin construction uses the gl Reindex refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalIsomorphismProperties.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalIsomorphismProperties.lean#L23-L25

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

theorem GlobalTheory.CompanionTheory.TyFin.glReindex_refl (g : GL α K) : glReindex K (Equiv.refl α) g = g := by sorry
