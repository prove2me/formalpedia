-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_frobIp
-- name    : GlobalTheory.CompanionTheory.TyFin.frobIp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:43.486134+00:00
-- url     : https://prove2.me/theorems/023181fb-b318-4405-a1fd-ade88d9956bc
-- title:
--   Ty Fin: frob Ip
-- statement:
--   The Ty Fin construction uses the frob Ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FrobeniusReciprocityInnerProduct.lean#L15-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FrobeniusReciprocityInnerProduct.lean#L15-L57

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.frobIp : ReciprocityTheory.Ty.Fin.St.FrobIp := by sorry
