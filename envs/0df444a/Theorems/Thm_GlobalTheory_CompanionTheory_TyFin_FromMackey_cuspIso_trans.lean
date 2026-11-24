-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_cuspIso_trans
-- name    : GlobalTheory.CompanionTheory.TyFin.FromMackey.cuspIso_trans
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:37.409806+00:00
-- url     : https://prove2.me/theorems/a2ff87c8-866b-4e4b-8f6b-042cb668b078
-- title:
--   From Mackey: cusp Iso trans
-- statement:
--   The From Mackey construction uses the cusp Iso trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L54-L58

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.FromMackey
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

theorem GlobalTheory.CompanionTheory.TyFin.FromMackey.cuspIso_trans {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    {nu : FDRep ℂ (GL γ K)} (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu := by sorry
