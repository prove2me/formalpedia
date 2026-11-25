-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_fromMackey
-- name    : GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:50.071139+00:00
-- url     : https://prove2.me/theorems/918a2cc9-dd6a-4551-87a1-3f29231dba46
-- title:
--   From Mackey: from Mackey
-- statement:
--   The From Mackey construction uses the from Mackey property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L100-L101

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
variable {K}

theorem GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey : ReciprocityTheory.Ty.Fin.St.FromMackey := by sorry
